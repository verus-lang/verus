use yansi::Paint;

use crate::context::SmtSolver;
use crate::smt_batch::BatchSolver;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};

struct SolverInfo {
    executable_name: &'static str,
    env_path_var: &'static str,
}

impl SolverInfo {
    pub fn new(solver: &SmtSolver) -> Self {
        match solver {
            SmtSolver::Z3 => SolverInfo { executable_name: "z3", env_path_var: "VERUS_Z3_PATH" },
            SmtSolver::Cvc5 => {
                SolverInfo { executable_name: "cvc5", env_path_var: "VERUS_CVC5_PATH" }
            }
            SmtSolver::Sundance => {
                SolverInfo { executable_name: "sundance-smt", env_path_var: "VERUS_SUNDANCE_PATH" }
            }
        }
    }

    pub fn executable(&self) -> String {
        if let Ok(path) = std::env::var(self.env_path_var) {
            path
        } else if cfg!(windows) {
            self.executable_name.to_string() + ".exe"
        } else {
            self.executable_name.to_string()
        }
    }
}

pub struct SmtProcess {
    requests: Option<Sender<Vec<u8>>>,
    backend: Backend,
    transcript_log: Option<Box<dyn std::io::Write>>,
}

type PipeResponses = Receiver<(BufReader<ChildStdout>, Vec<String>)>;

enum Backend {
    /// A solver process that reads commands from stdin (Z3, cvc5)
    Interactive {
        responses_buf_recv: Option<(BufReader<ChildStdout>, PipeResponses)>,
        recv_requests: Sender<BufReader<ChildStdout>>,
        child: Child,
    },
    /// A solver that is run once per check-sat on a complete script (Sundance);
    /// see `crate::smt_batch`
    Batch { responses: Receiver<Vec<String>>, worker: Option<std::thread::JoinHandle<()>> },
}

const DONE: &str = "<<DONE>>";
const DONE_QUOTED: &str = "\"<<DONE>>\"";

/// A separate thread writes data to the SMT solver over a pipe.
/// (Rust's documentation says you need a separate thread; otherwise, it lets the pipes deadlock.)
pub(crate) fn writer_thread(requests: Receiver<Vec<u8>>, mut smt_pipe_stdin: ChildStdin) {
    while let Ok(req) = requests.recv() {
        smt_pipe_stdin
            .write_all(&req)
            .and_then(|_| writeln!(&smt_pipe_stdin))
            // Ask the solver to print DONE, so we know when it is done
            .and_then(|_| writeln!(&smt_pipe_stdin, "(echo \"{}\")", DONE))
            .and_then(|_| smt_pipe_stdin.flush())
            // The solver process could die unexpectedly.  In that case, we die too:
            .expect("IO error: failure when sending data to solver process across pipe");
    }
    // Exit when the other side closes the channel
}

/// A separate thread read data from the SMT solver over a pipe.
fn reader_thread(
    recv_requests: Receiver<BufReader<ChildStdout>>,
    responses: Sender<(BufReader<ChildStdout>, Vec<String>)>,
    solver: SmtSolver,
) {
    while let Ok(mut smt_pipe_stdout) = recv_requests.recv() {
        let mut lines = Vec::new();
        let mut empty_lines = 0;
        loop {
            let mut line = String::new();
            smt_pipe_stdout
                .read_line(&mut line)
                // The solver process could die unexpectedly.  In that case, we die too:
                .expect("IO error: failure when receiving data from solver process across pipe");
            line = line.replace("\n", "").replace("\r", "");
            if line == "" {
                empty_lines += 1;
            } else {
                empty_lines = 0;
                if line
                    == match solver {
                        SmtSolver::Z3 => DONE,
                        SmtSolver::Cvc5 => DONE_QUOTED,
                        SmtSolver::Sundance => unreachable!("Sundance runs in batch mode"),
                    }
                {
                    responses
                        .send((smt_pipe_stdout, lines))
                        .expect("internal error: solver reader thread failure");
                    break;
                }
            }
            if empty_lines > 2 {
                panic!("Got too many empty lines!");
            }
            lines.push(line);
        }
    }
}

impl SmtProcess {
    pub fn launch(solver: &SmtSolver, transcript_log: Option<Box<dyn std::io::Write>>) -> Self {
        let solver_info = SolverInfo::new(solver);
        let mut command = std::process::Command::new(solver_info.executable());
        match solver {
            SmtSolver::Z3 => command.args(["-smt2", "-in"]),
            SmtSolver::Cvc5 => command.args([
                "--no-interactive",    // We don't need a human interface
                "--produce-models",    // Needed for error reporting
                "--quant-dsplit=none", // Recommended by Andrew Reynolds (@ajreynol)
                "--no-cbqi",           // Recommended by Andrew Reynolds (@ajreynol)
                "--user-pat=strict",   // Recommended by Andrew Reynolds (@ajreynol)
            ]),
            // Run once here to get the version and to check that the executable exists
            SmtSolver::Sundance => command.arg("--version"),
        };
        let mut child = match command
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
        {
            Ok(child) => child,
            Err(err) => {
                eprintln!(
                    "{}",
                    format!(
                        "error: could not execute {} process ({})",
                        solver_info.executable_name, err
                    )
                    .red()
                );
                eprintln!(
                    "help: {name} needs to be in the PATH, or the environment variable {var} must be set to the path of the {name} executable",
                    name = solver_info.executable_name,
                    var = solver_info.env_path_var
                );
                std::process::exit(128);
            }
        };
        if matches!(solver, SmtSolver::Sundance) {
            return Self::launch_batch(solver_info, child, transcript_log);
        }
        let smt_pipe_stdout = BufReader::new(child.stdout.take().expect("take stdout"));
        let child_stdin = child.stdin.take().expect("take stdin");
        let (requests_sender, requests_receiver) = channel();
        let (responses_sender, responses_receiver) = channel();
        let (recv_responses_sender, recv_responses_receiver) = channel();
        let solver_clone = solver.clone();
        std::thread::spawn(move || writer_thread(requests_receiver, child_stdin));
        std::thread::spawn(move || {
            reader_thread(recv_responses_receiver, responses_sender, solver_clone)
        });
        SmtProcess {
            requests: Some(requests_sender),
            backend: Backend::Interactive {
                responses_buf_recv: Some((smt_pipe_stdout, responses_receiver)),
                recv_requests: recv_responses_sender,
                child,
            },
            transcript_log,
        }
    }

    /// `version_child` is the solver running with `--version`
    fn launch_batch(
        solver_info: SolverInfo,
        version_child: Child,
        transcript_log: Option<Box<dyn std::io::Write>>,
    ) -> Self {
        let output = version_child.wait_with_output().expect("failed to run solver");
        // e.g. "sundance-smt 0.2.0"
        let version = String::from_utf8_lossy(&output.stdout)
            .split_whitespace()
            .last()
            .unwrap_or("unknown")
            .to_string();
        let args = vec![
            // Verus emits triggers for its quantifiers, but do not panic if some are missing
            "--infer-triggers".to_string(),
        ];
        let mut batch = BatchSolver::new(solver_info.executable(), args, version);
        let (requests_sender, requests_receiver) = channel::<Vec<u8>>();
        let (responses_sender, responses_receiver) = channel();
        let worker = std::thread::spawn(move || {
            while let Ok(req) = requests_receiver.recv() {
                if responses_sender.send(batch.process(&req)).is_err() {
                    break;
                }
            }
        });
        SmtProcess {
            requests: Some(requests_sender),
            backend: Backend::Batch { responses: responses_receiver, worker: Some(worker) },
            transcript_log,
        }
    }

    pub(crate) fn set_transcript_log(&mut self, writer: Box<dyn std::io::Write>) {
        self.transcript_log = Some(writer);
    }

    /// Send commands to the solver, wait for acknowledgement, and return responses
    pub(crate) fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        self.send_commands_async(commands).wait()
    }

    /// Send commands to the solver
    pub(crate) fn send_commands_async<'a>(&'a mut self, commands: Vec<u8>) -> CommandsHandle<'a> {
        // Send request to writer thread
        if let Some(writer) = &mut self.transcript_log {
            writeln!(writer, ";;;>>> QUERY").unwrap();
            writer.write_all(&commands).unwrap();
            writeln!(writer, ";;;<<<").unwrap();
            writer.flush().unwrap();
        }
        self.requests
            .as_mut()
            .unwrap()
            .send(commands)
            .expect("internal error: failed to send to writer thread");

        let receiver = match &mut self.backend {
            Backend::Interactive { responses_buf_recv, recv_requests, .. } => {
                let (smt_pipe_stdout, receiver) = responses_buf_recv
                    .take()
                    .expect("internal error: wait on the CommandsHandle first");

                // Send read request to reader thread
                recv_requests
                    .send(smt_pipe_stdout)
                    .expect("internal error: failed to send to reader thread");
                Some(receiver)
            }
            Backend::Batch { .. } => None,
        };

        CommandsHandle { smt_process: self, receiver }
    }
}

pub struct CommandsHandle<'a> {
    smt_process: &'a mut SmtProcess,
    /// The pipe reader's response channel (`None` for `Backend::Batch`)
    receiver: Option<PipeResponses>,
}

impl<'a> CommandsHandle<'a> {
    fn log_result(&mut self, result: &Vec<String>) {
        if let Some(writer) = &mut self.smt_process.transcript_log {
            writeln!(writer, ";;;>>> RESPONSE").unwrap();
            for line in result {
                writeln!(writer, "{}", line).unwrap();
            }
            writeln!(writer, ";;;<<<").unwrap();
            writer.flush().unwrap();
        }
    }

    /// Wait for the response (forever if `timeout` is `None`); return `None` on timeout
    fn recv(&mut self, timeout: Option<std::time::Duration>) -> Option<Vec<String>> {
        fn recv<T>(r: &Receiver<T>, timeout: Option<std::time::Duration>) -> Option<T> {
            let result = match timeout {
                None => r.recv().map_err(|_| RecvTimeoutError::Disconnected),
                Some(timeout) => r.recv_timeout(timeout),
            };
            match result {
                Ok(t) => Some(t),
                Err(RecvTimeoutError::Timeout) => None,
                Err(RecvTimeoutError::Disconnected) => {
                    panic!("internal error: solver reader thread disconnected")
                }
            }
        }
        let result = match &mut self.smt_process.backend {
            Backend::Interactive { responses_buf_recv, .. } => {
                let receiver = self.receiver.take().expect("receiver");
                match recv(&receiver, timeout) {
                    Some((smt_pipe_stdout, result)) => {
                        *responses_buf_recv = Some((smt_pipe_stdout, receiver));
                        Some(result)
                    }
                    None => {
                        self.receiver = Some(receiver);
                        None
                    }
                }
            }
            Backend::Batch { responses, .. } => recv(responses, timeout),
        };
        if let Some(result) = &result {
            self.log_result(result);
        }
        result
    }

    pub fn wait(mut self) -> Vec<String> {
        self.recv(None).expect("no timeout")
    }

    pub fn wait_timeout(mut self, timeout: std::time::Duration) -> Result<Vec<String>, Self> {
        match self.recv(Some(timeout)) {
            Some(result) => Ok(result),
            None => Err(self),
        }
    }
}

impl Drop for SmtProcess {
    fn drop(&mut self) {
        // send EOF to stdin
        std::mem::drop(self.requests.take());
        match &mut self.backend {
            Backend::Interactive { child, .. } => {
                if let Err(e) = child.wait() {
                    panic!("smt process exited with error: {:?}", e);
                }
            }
            Backend::Batch { worker, .. } => {
                if let Some(worker) = worker.take() {
                    let _ = worker.join();
                }
            }
        }
    }
}
