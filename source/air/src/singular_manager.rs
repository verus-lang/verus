use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

// this is only used in print command
pub const DONE: &str = "<<Singular DONE>>";

pub struct SingularManager {
    pub singular_executable_name: String,
}

pub struct SingularProcess {
    requests: Option<Sender<Vec<u8>>>,
    singular_pipe_stdout: BufReader<ChildStdout>,
    child: std::process::Child,
}

/// this is similar to writer_thread in smt_process.rs
/// the way we ask for acknowledgement is slightly different
fn singular_writer_thread(requests: Receiver<Vec<u8>>, mut singular_pipe_stdin: ChildStdin) {
    while let Ok(req) = requests.recv() {
        singular_pipe_stdin
            .write_all(&req)
            // ask for acknowledgement
            .and_then(|_| writeln!(&singular_pipe_stdin, "print (\"{}\");", DONE))
            .and_then(|_| singular_pipe_stdin.flush())
            .expect("IO error: failure when sending data to Singular process across pipe");
    }
    singular_pipe_stdin.write_all(b"quit;\n").expect("IO error: failure quitting Singular process");
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
            // .arg("--no-tty") // these options are potentially useful for debugging purposes
            // .arg("--no-shell")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .expect("could not execute Singular process");

        let child_stdout = child.stdout.take().expect("take stdout");
        let singular_pipe_stdout = BufReader::new(child_stdout);

        let child_stdin = child.stdin.take().expect("take stdin");
        let (sender, receiver) = channel();
        std::thread::spawn(move || singular_writer_thread(receiver, child_stdin));
        SingularProcess { requests: Some(sender), singular_pipe_stdout, child }
    }
}

impl SingularProcess {
    pub fn send_commands(&mut self, commands: Vec<u8>) -> Vec<String> {
        // Send request to writer thread
        self.requests
            .as_mut()
            .unwrap()
            .send(commands)
            .expect("internal error: failed to send to writer thread");
        let mut lines = Vec::new();
        loop {
            let mut line = String::new();
            self.singular_pipe_stdout
                .read_line(&mut line)
                .expect("IO error: failure when receiving data to singular process across pipe");
            line = line.replace("\n", "").replace("\r", "");
            if line == DONE || line == "" {
                break;
            }
            lines.push(line);
        }
        lines
    }
}

impl Drop for SingularProcess {
    fn drop(&mut self) {
        std::mem::drop(self.requests.take());
        if let Err(e) = self.child.wait() {
            panic!("Singular process exited with error: {:?}", e);
        }
    }
}

pub fn log_singular(context: &mut crate::context::Context, query: &String, _func_span: &str) {
    context.air_initial_log.comment(&query);
    context.air_middle_log.comment(&query);
    context.air_final_log.comment(&query);

    // TODO restore these context.singular_log.as_mut().unwrap().write(format!("// {}\n", func_span).as_bytes()).unwrap();
    // TODO restore these context.singular_log.as_mut().unwrap().write(format!("{}\n", query).as_bytes()).unwrap();
}
