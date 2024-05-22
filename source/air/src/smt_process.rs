use crate::context::SmtSolver;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

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
    responses_buf_recv:
        Option<(BufReader<ChildStdout>, Receiver<(BufReader<ChildStdout>, Vec<String>)>)>,
    recv_requests: Sender<BufReader<ChildStdout>>,
    child: Child,
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
            // Ask Z3 to print DONE, so we know when it is done
            .and_then(|_| writeln!(&smt_pipe_stdin, "(echo \"{}\")", DONE))
            .and_then(|_| smt_pipe_stdin.flush())
            // The Z3 process could die unexpectedly.  In that case, we die too:
            .expect("IO error: failure when sending data to Z3 process across pipe");
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
                // The Z3 process could die unexpectedly.  In that case, we die too:
                .expect("IO error: failure when receiving data to Z3 process across pipe");
            line = line.replace("\n", "").replace("\r", "");
            if line == "" {
                empty_lines += 1;
            } else {
                empty_lines = 0;
                if line
                    == match solver {
                        SmtSolver::Z3 => DONE,
                        SmtSolver::Cvc5 => DONE_QUOTED,
                    }
                {
                    responses
                        .send((smt_pipe_stdout, lines))
                        .expect("internal error: Z3 reader thread failure");
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
    pub fn launch(solver: &SmtSolver) -> Self {
        let solver_info = SolverInfo::new(solver);
        let mut child = match std::process::Command::new(solver_info.executable())
            .args(match solver {
                SmtSolver::Z3 => vec!["-smt2", "-in"],
                SmtSolver::Cvc5 => vec![
                    "--no-interactive",    // We don't need a human interface
                    "--produce-models",    // Needed for error reporting
                    "--quant-dsplit=none", // Recommended by Andrew Reynolds (@ajreynol)
                    "--no-cbqi",           // Recommended by Andrew Reynolds (@ajreynol)
                    "--user-pat=strict",   // Recommended by Andrew Reynolds (@ajreynol)
                    "--rlimit",
                    "1666666", // ~= 5s
                ],
            })
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
        {
            Ok(child) => child,
            Err(err) => {
                eprintln!(
                    "{}",
                    yansi::Paint::red(format!(
                        "error: could not execute {} process ({})",
                        solver_info.executable_name, err
                    ))
                );
                eprintln!(
                    "help: {name} needs to be in the PATH, or the environment variable {var} must be set to the path of the {name} executable",
                    name = solver_info.executable_name,
                    var = solver_info.env_path_var
                );
                std::process::exit(128);
            }
        };
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
            responses_buf_recv: Some((smt_pipe_stdout, responses_receiver)),
            recv_requests: recv_responses_sender,
            child: child,
        }
    }

    /// Send commands to Z3, wait for Z3 to acknowledge commands, and return responses
    pub(crate) fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        self.send_commands_async(commands).wait()
    }

    /// Send commands to Z3
    pub(crate) fn send_commands_async<'a>(&'a mut self, commands: Vec<u8>) -> CommandsHandle<'a> {
        // Send request to writer thread
        self.requests
            .as_mut()
            .unwrap()
            .send(commands)
            .expect("internal error: failed to send to writer thread");

        let (smt_pipe_stdout, receiver) = self
            .responses_buf_recv
            .take()
            .expect("internal error: wait on the CommandsHandle first");

        // Send read request to reader thread
        self.recv_requests
            .send(smt_pipe_stdout)
            .expect("internal error: failed to send to reader thread");

        CommandsHandle { smt_process: self, receiver }
    }
}

pub struct CommandsHandle<'a> {
    smt_process: &'a mut SmtProcess,
    receiver: std::sync::mpsc::Receiver<(BufReader<ChildStdout>, Vec<String>)>,
}

impl<'a> CommandsHandle<'a> {
    pub fn wait(self) -> Vec<String> {
        let (smt_pipe_stdout, result) =
            self.receiver.recv().expect("internal error: Z3 reader thread failure");
        self.smt_process.responses_buf_recv = Some((smt_pipe_stdout, self.receiver));
        result
    }

    pub fn wait_timeout(self, timeout: std::time::Duration) -> Result<Vec<String>, Self> {
        match self.receiver.recv_timeout(timeout) {
            Ok((smt_pipe_stdout, result)) => {
                self.smt_process.responses_buf_recv = Some((smt_pipe_stdout, self.receiver));
                Ok(result)
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Err(self),
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                panic!("internal error: Z3 reader thread disconnected")
            }
        }
    }
}

impl Drop for SmtProcess {
    fn drop(&mut self) {
        // send EOF to stdin
        std::mem::drop(self.requests.take());
        if let Err(e) = self.child.wait() {
            panic!("smt process exited with error: {:?}", e);
        }
    }
}
