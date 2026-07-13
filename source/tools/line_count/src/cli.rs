use clap::Parser;
use line_count_lib::config::Config;
use line_count_lib::config::RunMode;

#[derive(Clone, Debug, Parser)]
pub struct LineCountArgs {
    #[clap(flatten)]
    pub config: Config,

    /// Parse one file, instead of using the DEPS_FILE.d file produced by rustc
    #[arg(long, conflicts_with = "dir")]
    pub one_file: bool,

    /// Parse dirs, instead of using the DEPS_FILE.d file produced by rustc
    #[arg(long, conflicts_with = "one_file")]
    pub dir: bool,

    /// Paths to be counted. Semantics depends on mode of usage
    #[arg(num_args = 1..)]
    pub paths: Vec<std::path::PathBuf>,
}

impl LineCountArgs {
    /// Validate the arguments
    /// Returns an error with a message to be printed to the user
    pub fn validate(&self) -> Result<(), String> {
        if !self.dir && self.paths.len() > 1 {
            if self.one_file {
                Err(format!(
                    "with mode --one-file, we can only have one single file being counted, not {}",
                    self.paths.len()
                ))
            } else {
                Err(format!(
                    "in dep mode, we can only take in the single DEPS_FILE.d file, not {} files",
                    self.paths.len()
                ))
            }
        } else {
            Ok(())
        }
    }

    /// Separate LineCountArgs in a config and a run mode
    pub fn separate_config(self) -> (Config, RunMode) {
        let run_mode = if self.one_file {
            RunMode::OneFile(self.paths.into_iter().next().expect("we know paths are not empty"))
        } else if self.dir {
            RunMode::Dir(self.paths)
        } else {
            RunMode::DepsPath(self.paths.into_iter().next().expect("we know paths is not empty"))
        };

        (self.config, run_mode)
    }
}
