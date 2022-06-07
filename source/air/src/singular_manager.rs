use crate::smt_process::writer_thread;
use std::io::{BufRead, BufReader};
use std::process::ChildStdout;
use std::sync::mpsc::{channel, Sender};

pub struct SingularManager {
    pub singular_executable_name: String,
}

pub struct SingularProcess {
    requests: Sender<Vec<u8>>,
    singular_pipe_stdout: BufReader<ChildStdout>,
}

impl SingularManager {
    pub fn new() -> Self {
        SingularManager {
            singular_executable_name: std::env::var("VERUS_SINGULAR_PATH")
                .expect("cannot find singular path, to use integer_ring functionality, please provide VERUS_SINGULAR_PATH"),
        }
    }
    pub fn launch(&self) -> SingularProcess {
        let mut child = std::process::Command::new(&self.singular_executable_name)
            .arg("--quiet")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("could not execute Singular process");
        let singular_pipe_stdout = BufReader::new(child.stdout.take().expect("take stdout"));
        let child_stdin = child.stdin.take().expect("take stdin");
        let (sender, receiver) = channel();
        std::thread::spawn(move || writer_thread(receiver, child_stdin));
        SingularProcess { requests: sender, singular_pipe_stdout }
    }
}

impl SingularProcess {
    pub fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        // Send request to writer thread
        self.requests.send(commands).expect("internal error: failed to send to writer thread");
        let mut lines = Vec::new();
        let mut line = String::new();
        self.singular_pipe_stdout
            .read_line(&mut line)
            .expect("IO error: failure when receiving data to singular process across pipe");
        line = line.replace("\n", "").replace("\r", "");
        lines.push(line);
        lines
    }
}
