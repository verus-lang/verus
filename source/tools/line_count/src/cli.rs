use clap::Parser;
use line_count_lib::config::Config;
use line_count_lib::config::RunMode;

#[derive(Clone, Debug, Parser)]
pub struct LineCountArgs {
    #[clap(flatten)]
    pub config: Config,

    /// Parse the DEPS_FILE.d file produced by rustc, finding the crate's paths from that source
    #[arg(long)]
    pub deps: bool,

    /// Paths to be counted. Can only be 1 in `--deps` mode
    #[arg(num_args = 1..)]
    pub paths: Vec<std::path::PathBuf>,
}

impl LineCountArgs {
    /// Validate the arguments
    /// Returns an error with a message to be printed to the user
    pub fn validate(&self) -> Result<(), String> {
        if self.deps && self.paths.len() > 1 {
            Err(format!(
                "in deps mode, we can only take in the single DEPS_FILE.d file, not {} files",
                self.paths.len()
            ))
        } else {
            Ok(())
        }
    }

    /// Separate LineCountArgs in a config and a run mode
    pub fn separate_config(self) -> (Config, RunMode) {
        let run_mode = if self.deps {
            RunMode::DepsPath(self.paths.into_iter().next().expect("we know paths is not empty"))
        } else {
            RunMode::Files(self.paths)
        };

        (self.config, run_mode)
    }
}
