use std::io::{BufRead, BufReader, Write};
use std::process::{ChildStdin, ChildStdout};
use std::sync::mpsc::{channel, Receiver, Sender};

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
            // .arg("--no-tty")
            .arg("--quiet")
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
        SingularProcess { requests: sender, singular_pipe_stdout }
    }
}

fn singular_writer_thread(requests: Receiver<Vec<u8>>, mut singular_pipe_stdin: ChildStdin) {
    while let Ok(req) = requests.recv() {
        singular_pipe_stdin
            .write_all(&req)
            .and_then(|_| writeln!(&singular_pipe_stdin))
            // .and_then(|_| writeln!(&singular_pipe_stdin, "print("ok");", DONE))
            .and_then(|_| singular_pipe_stdin.flush())
            // The Singular process could die unexpectedly. In that case, we die too:
            .expect("IO error: failure when sending data to Singular process across pipe");
    }
    // Exit when the other side closes the channel
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

pub fn log_singular(
    context: &mut crate::context::Context,
    query: &String,
    func_span: &crate::ast::Span,
) {
    context.air_initial_log.comment(&query);
    context.air_middle_log.comment(&query);
    context.air_final_log.comment(&query);

    context
        .singular_log
        .as_mut()
        .unwrap()
        .write(format!("// {}\n", func_span.as_string).as_bytes())
        .unwrap();
    context.singular_log.as_mut().unwrap().write(format!("{}\n", query).as_bytes()).unwrap();
}
