use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

pub(crate) struct SmtProcess {
    requests: Sender<Vec<u8>>,
    smt_pipe_stdout: Option<BufReader<ChildStdout>>,
}

const DONE: &str = "<<DONE>>";

/// A separate thread writes data to the SMT solver over a pipe.
/// (Rust's documentation says you need a separate thread; otherwise, it lets the pipes deadlock.)
fn writer_thread(requests: Receiver<Vec<u8>>, mut smt_pipe_stdin: ChildStdin) {
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

impl SmtProcess {
    pub(crate) fn launch(smt_executable_name: &String) -> Self {
        let mut child = std::process::Command::new(smt_executable_name)
            .args(&["-smt2", "-in"])
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("could not execute Z3 process");
        let smt_pipe_stdout = BufReader::new(child.stdout.take().expect("take stdout"));
        let child_stdin = child.stdin.take().expect("take stdin");
        let (sender, receiver) = channel();
        std::thread::spawn(move || writer_thread(receiver, child_stdin));
        SmtProcess { requests: sender, smt_pipe_stdout: Some(smt_pipe_stdout) }
    }

    /// Send commands to Z3, wait for Z3 to acknowledge commands, and return responses
    pub(crate) fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        self.send_commands_async(commands).wait()
    }

    /// Send commands to Z3
    pub(crate) fn send_commands_async<'a>(&'a mut self, commands: Vec<u8>) -> CommandsHandle<'a> {
        // Send request to writer thread
        self.requests.send(commands).expect("internal error: failed to send to writer thread");

        let smt_pipe_stdout =
            self.smt_pipe_stdout.take().expect("internal error: wait on the CommandsHandle first");
        let (sender, receiver) = std::sync::mpsc::channel();

        let join_handle = std::thread::spawn(move || {
            let mut smt_pipe_stdout = smt_pipe_stdout;
            let mut lines = Vec::new();
            loop {
                let mut line = String::new();
                smt_pipe_stdout
                    .read_line(&mut line)
                    // The Z3 process could die unexpectedly.  In that case, we die too:
                    .expect("IO error: failure when receiving data to Z3 process across pipe");
                line = line.replace("\n", "").replace("\r", "");
                if line == DONE {
                    sender.send(lines).expect("internal error: Z3 reader thread failure");
                    break smt_pipe_stdout;
                }
                lines.push(line);
            }
        });

        CommandsHandle { smt_process: self, join_handle, receiver }
    }
}

pub struct CommandsHandle<'a> {
    smt_process: &'a mut SmtProcess,
    join_handle: std::thread::JoinHandle<BufReader<ChildStdout>>,
    receiver: std::sync::mpsc::Receiver<Vec<String>>,
}

impl<'a> CommandsHandle<'a> {
    pub fn wait(self) -> Vec<String> {
        let result = self.receiver.recv().expect("internal error: Z3 reader thread failure");
        self.smt_process.smt_pipe_stdout =
            Some(self.join_handle.join().expect("internal error: Z3 reader thread failure"));
        result
    }

    pub fn wait_timeout(self, timeout: std::time::Duration) -> Result<Vec<String>, Self> {
        match self.receiver.recv_timeout(timeout) {
            Ok(result) => {
                self.smt_process.smt_pipe_stdout = Some(
                    self.join_handle.join().expect("internal error: Z3 reader thread failure"),
                );
                Ok(result)
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Err(self),
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                panic!("internal error: Z3 reader thread disconnected")
            }
        }
    }
}
