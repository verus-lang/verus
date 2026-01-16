use std::path::Path;
use std::process::Command;

use crate::cli::FeaturesOptions;
use crate::cli::VargoOptions;
use crate::cli::VerusFeatures;
use crate::macros::info;
use crate::VargoContext;

use crate::VSTD_FILES;

mod build;
mod check;
mod clean;
mod clippy;
mod cmd;
mod fmt;
mod metadata;
mod nextest;
mod run;
mod test;
mod update;

use anyhow::Context;
pub use build::build;
pub use check::check;
pub use clean::clean;
pub use clippy::clippy;
pub use cmd::cmd;
pub use fmt::fmt;
pub use metadata::metadata;
pub use nextest::nextest_run;
pub use run::run;
pub use test::test;
pub use update::update;

pub(crate) trait AddOptions {
    fn add_options(&self, cargo: &mut std::process::Command);
    fn cmd_name(&self) -> &str;
}

pub(crate) fn cargo_command(options: &VargoOptions, context: &VargoContext) -> Command {
    let mut cargo = std::process::Command::new("cargo");
    cargo
        .env("RUST_MIN_STACK", test_rust_min_stack())
        .env("RUSTC_BOOTSTRAP", "1")
        .env("VERUS_IN_VARGO", "1")
        .env(
            "VARGO_TARGET_DIR",
            &context.target_verus_artifact_dir_absolute,
        )
        .env("RUSTFLAGS", rust_flags());

    if options.cargo_options.offline {
        cargo.arg("--offline");
    }
    if options.cargo_options.verbose > 0 {
        cargo.arg(format!(
            "-{}",
            "v".repeat(options.cargo_options.verbose as usize)
        ));
    }
    cargo.args(["--color", &format!("{}", options.cargo_options.color)]);

    cargo
}

pub(crate) fn cargo_run<Cmd: AddOptions>(
    options: &VargoOptions,
    context: &VargoContext,
    cmd: &Cmd,
) -> anyhow::Result<()> {
    let mut cargo = cargo_command(options, context);
    cmd.add_options(&mut cargo);
    log_command(&cargo, options.vargo_verbose);

    let status = cargo
        .status()
        .with_context(|| format!("could not execute `cargo {}`", cmd.cmd_name()))?;

    if !status.success() {
        if let Some(code) = status.code() {
            anyhow::bail!("`cargo {}` returned status code {}", cmd.cmd_name(), code)
        } else {
            anyhow::bail!("`cargo {}` was terminated by a signal", cmd.cmd_name(),)
        }
    }

    Ok(())
}

fn test_rust_min_stack() -> String {
    (20 * 1024 * 1024).to_string()
}

pub(crate) fn log_command(cmd: &std::process::Command, verbose: bool) {
    use crate::VARGO_NEST;
    use yansi::Paint;
    if verbose {
        let vargo_nest = *VARGO_NEST.read().unwrap();
        eprintln!(
            "{}",
            format!("vargo running [{}]: {:?}", vargo_nest, cmd).magenta()
        );
    }
}

fn rust_flags() -> String {
    const NEEDED_CFGS: [&str; 4] = [
        "--cfg proc_macro_span",
        "--cfg verus_keep_ghost",
        "--cfg span_locations",
        "--cfg procmacro2_semver_exempt",
    ];

    let user_rustflags = std::env::var("RUSTFLAGS").unwrap_or_default();
    NEEDED_CFGS
        .into_iter()
        .chain(std::iter::once(user_rustflags.as_str()))
        .collect::<Vec<_>>()
        .join(" ")
}

pub(crate) fn clean_vstd(target_verus_dir: impl AsRef<Path>) -> anyhow::Result<()> {
    let target_verus_dir = target_verus_dir.as_ref();
    for f in VSTD_FILES.iter() {
        let f = target_verus_dir.join(f);
        if f.is_file() && f.exists() {
            info!("removing {}", f.display());
            std::fs::remove_file(&f)
                .with_context(|| format!("could not delete file {}", f.display()))?;
        }
    }
    Ok(())
}

impl FeaturesOptions {
    pub(crate) fn add_options(&self, cargo: &mut std::process::Command) {
        if self.no_default_features {
            cargo.arg("--no-default-features");
        }

        for feature in &self.features {
            cargo.arg("--features");
            cargo.arg(format!("{feature}"));
        }
    }

    pub(crate) fn filter_feature_list(&mut self, accepted: &[VerusFeatures]) {
        self.features.retain(|f| accepted.contains(f));
    }
}
