use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

pub(crate) struct SmtProcess {
    requests: Sender<Vec<u8>>,
    smt_pipe_stdout: BufReader<ChildStdout>,
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
        SmtProcess { requests: sender, smt_pipe_stdout }
    }

    /// Send commands to Z3, wait for Z3 to acknowledge commands, and return responses
    pub(crate) fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        // Send request to writer thread
        self.requests.send(commands).expect("internal error: failed to send to writer thread");

        // Loop until we receive the DONE message that we asked Z3 to echo back
        let mut lines = Vec::new();
        loop {
            let mut line = String::new();
            self.smt_pipe_stdout
                .read_line(&mut line)
                // The Z3 process could die unexpectedly.  In that case, we die too:
                .expect("IO error: failure when receiving data to Z3 process across pipe");
            line = line.replace("\n", "").replace("\r", "");
            if line == DONE {
                return lines;
            }
            lines.push(line);
        }
    }
}
