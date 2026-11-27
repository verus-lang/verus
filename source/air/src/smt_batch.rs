//! Support for SMT solvers without an interactive mode (currently Sundance).
//!
//! Such a solver reads one complete SMT-LIB script from a file and answers a single
//! `check-sat`. `BatchSolver` lets AIR drive it like an interactive solver process:
//! it keeps the declarations and assertions of each open `push`/`pop` scope, and at
//! each `check-sat` it writes the open scopes to a temporary file and runs the solver
//! on that file. It answers the follow-up commands that AIR sends (`get-info`,
//! `get-model`, `echo`) itself.
//!
//! Batch solvers produce no models, so a failed query is reported for the whole
//! function rather than for the individual assertion that failed.

use std::io::Read;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// Prefix of the `check-sat` response line when the solver could not process the query
/// (for example because the query uses a theory that the solver does not support).
/// The rest of the line is a message for the user.
pub(crate) const SOLVER_FAILURE_PREFIX: &str = "batch-solver-failure: ";

/// After the solver's own timeout has passed, wait this much longer before killing it.
const KILL_GRACE: Duration = Duration::from_secs(10);

static SCRIPT_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Sat,
    Unsat,
    Unknown { timed_out: bool },
}

pub(crate) struct BatchSolver {
    executable: String,
    args: Vec<String>,
    version: String,
    /// Commands in each open scope; `scopes[0]` is the outermost scope.
    scopes: Vec<Vec<String>>,
    /// Per-`check-sat` time limit in seconds, set with `(set-option :rlimit N)`; 0 means none.
    timeout_secs: u64,
    last_outcome: Option<Outcome>,
}

impl BatchSolver {
    pub(crate) fn new(executable: String, args: Vec<String>, version: String) -> Self {
        BatchSolver {
            executable,
            args,
            version,
            scopes: vec![Vec::new()],
            timeout_secs: 0,
            last_outcome: None,
        }
    }

    /// Process a request (a sequence of SMT-LIB commands) and return the response lines.
    pub(crate) fn process(&mut self, request: &[u8]) -> Vec<String> {
        let request = String::from_utf8_lossy(request);
        let mut responses = Vec::new();
        for command in split_commands(&request) {
            self.command(command, &mut responses);
        }
        responses
    }

    fn command(&mut self, command: &str, responses: &mut Vec<String>) {
        let mut words = command[1..command.len() - 1].split_whitespace();
        let head = words.next().unwrap_or("");
        let arg = words.next();
        match head {
            "push" => {
                for _ in 0..arg.and_then(|n| n.parse().ok()).unwrap_or(1) {
                    self.scopes.push(Vec::new());
                }
            }
            "pop" => {
                for _ in 0..arg.and_then(|n| n.parse().ok()).unwrap_or(1) {
                    assert!(self.scopes.len() > 1, "internal error: pop without matching push");
                    self.scopes.pop();
                }
            }
            "set-option" => {
                if arg == Some(":rlimit") {
                    self.timeout_secs = words.next().and_then(|n| n.parse().ok()).unwrap_or(0);
                }
                // Other options are meant for interactive solvers
            }
            "check-sat" => responses.push(self.check_sat()),
            "get-info" => responses.push(match arg {
                Some(":version") => format!("(:version \"{}\")", self.version),
                Some(":reason-unknown") => match self.last_outcome {
                    Some(Outcome::Unknown { timed_out: true }) => "(:reason-unknown timeout)",
                    _ => "(:reason-unknown incomplete)",
                }
                .to_string(),
                _ => unsupported(head),
            }),
            "get-model" => responses.push("(error \"model is not available\")".to_string()),
            "echo" => {
                let s = command["(echo".len()..command.len() - 1].trim();
                responses.push(s.trim_matches('"').replace("\"\"", "\""));
            }
            "exit" => {}
            "get-value" | "get-unsat-core" | "check-sat-assuming" | "eval" => {
                responses.push(unsupported(head))
            }
            _ => self.scopes.last_mut().unwrap().push(command.to_string()),
        }
    }

    fn check_sat(&mut self) -> String {
        self.last_outcome = None;
        let path = std::env::temp_dir().join(format!(
            "verus-batch-{}-{}.smt2",
            std::process::id(),
            SCRIPT_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let mut script = String::new();
        for command in self.scopes.iter().flatten() {
            script.push_str(command);
            script.push('\n');
        }
        script.push_str("(check-sat)\n");
        if let Err(err) = std::fs::write(&path, script) {
            return format!("{}could not write {}: {}", SOLVER_FAILURE_PREFIX, path.display(), err);
        }
        let result = self.run(&path);
        let _ = std::fs::remove_file(&path);
        match result {
            Ok(outcome) => {
                self.last_outcome = Some(outcome);
                match outcome {
                    Outcome::Sat => "sat",
                    Outcome::Unsat => "unsat",
                    Outcome::Unknown { .. } => "unknown",
                }
                .to_string()
            }
            Err(msg) => format!("{}{}", SOLVER_FAILURE_PREFIX, msg),
        }
    }

    fn run(&self, path: &std::path::Path) -> Result<Outcome, String> {
        let start = Instant::now();
        let mut child = Command::new(&self.executable)
            .args(&self.args)
            .arg("--timeout")
            .arg(self.timeout_secs.to_string())
            .arg(path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|err| format!("could not execute {}: {}", self.executable, err))?;
        let stdout = read_in_thread(child.stdout.take().unwrap());
        let stderr = read_in_thread(child.stderr.take().unwrap());
        let deadline = (self.timeout_secs > 0)
            .then(|| start + Duration::from_secs(self.timeout_secs) + KILL_GRACE);
        let status = loop {
            if let Some(status) = child.try_wait().map_err(|err| err.to_string())? {
                break Some(status);
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        let stdout = stdout.join().unwrap_or_default();
        let stderr = stderr.join().unwrap_or_default();
        let Some(status) = status else {
            return Ok(Outcome::Unknown { timed_out: true });
        };
        let timed_out =
            self.timeout_secs > 0 && start.elapsed() >= Duration::from_secs(self.timeout_secs);
        match stdout.lines().map(str::trim).filter(|l| !l.is_empty()).last() {
            Some("sat") if status.success() => Ok(Outcome::Sat),
            Some("unsat") if status.success() => Ok(Outcome::Unsat),
            Some("unknown") if status.success() => Ok(Outcome::Unknown { timed_out }),
            _ => {
                let msg: Vec<&str> =
                    stderr.lines().map(str::trim).filter(|l| !l.is_empty()).take(3).collect();
                Err(format!("{} failed ({}): {}", self.executable, status, msg.join(" ")))
            }
        }
    }
}

fn unsupported(command: &str) -> String {
    format!("(error \"{} is not supported by batch solvers\")", command)
}

fn read_in_thread<R: Read + Send + 'static>(mut r: R) -> std::thread::JoinHandle<String> {
    std::thread::spawn(move || {
        let mut s = String::new();
        let _ = r.read_to_string(&mut s);
        s
    })
}

/// Split SMT-LIB text into its top-level commands, skipping comments.
fn split_commands(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut commands = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                // "" is an escaped quote inside a string literal
                while i < bytes.len() && !(bytes[i] == b'"' && bytes.get(i + 1) != Some(&b'"')) {
                    i += if bytes[i] == b'"' { 2 } else { 1 };
                }
            }
            b'|' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
            }
            b'(' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 {
                    commands.push(&text[start..=i]);
                }
            }
            _ => {}
        }
        i += 1;
    }
    commands
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split() {
        let text = "; c (\n(declare-fun |a)| () Int)\n(echo \"x)\"\"\") ;; (\n(push)";
        assert_eq!(
            split_commands(text),
            vec!["(declare-fun |a)| () Int)", "(echo \"x)\"\"\")", "(push)"]
        );
    }

    #[test]
    fn scopes() {
        let mut s = BatchSolver::new("solver".into(), vec![], "1.0".into());
        let r = s.process(b"(declare-const a Int)\n(push)\n(assert a)\n(push 2)\n(pop 2)\n");
        assert!(r.is_empty());
        assert_eq!(s.scopes, vec![vec!["(declare-const a Int)"], vec!["(assert a)"]]);
        s.process(b"(pop)\n(set-option :rlimit 7)");
        assert_eq!(s.scopes.len(), 1);
        assert_eq!(s.timeout_secs, 7);
        assert_eq!(
            s.process(b"(get-info :version)\n(echo \"<<DONE>>\")"),
            vec!["(:version \"1.0\")", "<<DONE>>"]
        );
    }
}
