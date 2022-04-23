use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

pub(crate) struct SmtProcess {
    requests: Sender<Vec<u8>>,
    responses_buf_recv:
        Option<(BufReader<ChildStdout>, Receiver<(BufReader<ChildStdout>, Vec<String>)>)>,
    recv_requests: Sender<BufReader<ChildStdout>>,
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

/// A separate thread read data from the SMT solver over a pipe.
fn reader_thread(
    recv_requests: Receiver<BufReader<ChildStdout>>,
    responses: Sender<(BufReader<ChildStdout>, Vec<String>)>,
) {
    while let Ok(mut smt_pipe_stdout) = recv_requests.recv() {
        let mut lines = Vec::new();
        loop {
            let mut line = String::new();
            smt_pipe_stdout
                .read_line(&mut line)
                // The Z3 process could die unexpectedly.  In that case, we die too:
                .expect("IO error: failure when receiving data to Z3 process across pipe");
            line = line.replace("\n", "").replace("\r", "");
            if line == DONE {
                responses
                    .send((smt_pipe_stdout, lines))
                    .expect("internal error: Z3 reader thread failure");
                break;
            }
            lines.push(line);
        }
    }
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
        let (requests_sender, requests_receiver) = channel();
        let (responses_sender, responses_receiver) = channel();
        let (recv_responses_sender, recv_responses_receiver) = channel();
        std::thread::spawn(move || writer_thread(requests_receiver, child_stdin));
        std::thread::spawn(move || reader_thread(recv_responses_receiver, responses_sender));
        SmtProcess {
            requests: requests_sender,
            responses_buf_recv: Some((smt_pipe_stdout, responses_receiver)),
            recv_requests: recv_responses_sender,
        }
    }

    /// Send commands to Z3, wait for Z3 to acknowledge commands, and return responses
    pub(crate) fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        self.send_commands_async(commands).wait()
    }

    /// Send commands to Z3
    pub(crate) fn send_commands_async<'a>(&'a mut self, commands: Vec<u8>) -> CommandsHandle<'a> {
        // Send request to writer thread
        self.requests.send(commands).expect("internal error: failed to send to writer thread");

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
