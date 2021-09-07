use crate::smt_process::SmtProcess;

pub struct SmtManager {
    smt_process: Option<SmtProcess>,
    smt_executable_name: String,
}

impl SmtManager {
    pub fn new() -> Self {
        let smt_executable_name = if let Ok(path) = std::env::var("DUST_Z3_PATH") {
            path
        } else {
            if cfg!(windows) { "z3.exe" } else { "z3" }.to_string()
        };
        SmtManager { smt_process: None, smt_executable_name }
    }

    pub fn set_smt_executable_name(&mut self, name: String) {
        self.smt_executable_name = name;
    }

    /// Launch the SMT process if it hasn't been started yet.
    /// Return the SmtProcess.
    pub(crate) fn get_smt_process(&mut self) -> &mut SmtProcess {
        if self.smt_process.is_none() {
            self.smt_process = Some(SmtProcess::launch(&self.smt_executable_name));
        }
        self.smt_process.as_mut().unwrap()
    }
}
