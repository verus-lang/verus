use std::ffi::OsStr;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context;
use regex::Regex;

use crate::cli::VargoFmt;
use crate::cli::VargoOptions;
use crate::commands::cargo_run;
use crate::commands::log_command;
use crate::commands::AddOptions;
use crate::macros::info;
use crate::macros::warning;
use crate::VargoContext;

const MINIMUM_VERUSFMT_VERSION: (u64, u64, u64) = (0, 5, 0);

impl AddOptions for VargoFmt {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("fmt");

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }

        cargo.args(["--", "--config", "style_edition=2024"]);
        cargo.args(&self.rustfmt_args);
    }

    fn cmd_name(&self) -> &str {
        "fmt"
    }
}

pub fn fmt(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoFmt,
) -> anyhow::Result<()> {
    if context.in_nextest {
        return Ok(());
    }

    cargo_run(options, context, vargo_cmd)?;

    format_rust_dir(
        Path::new("../dependencies/syn"),
        &vargo_cmd.rustfmt_args,
        options.cargo_options.verbose > 0,
    )?;
    format_rust_dir(
        Path::new("../dependencies/prettyplease"),
        &vargo_cmd.rustfmt_args,
        options.cargo_options.verbose > 0,
    )?;

    if !vargo_cmd.exclude.iter().any(|e| e.as_str() == "vstd") {
        format_vstd(options, vargo_cmd)?;
    }

    Ok(())
}

fn format_rust_dir(
    path: impl AsRef<Path>,
    rustfmt_args: &[impl AsRef<OsStr>],
    verbose: bool,
) -> anyhow::Result<()> {
    let path = path.as_ref();
    let path_filename = path.file_name().unwrap_or(OsStr::new("<unknown dir>"));
    info!("formatting {}", path_filename.display());
    let mut cargo_fmt = std::process::Command::new("cargo");
    cargo_fmt
        .current_dir(path)
        // TODO(bsdinis): these other libraries are not being formatted with style_edition=2024
        .args(["fmt", "--"])
        .args(rustfmt_args);
    log_command(&cargo_fmt, verbose);
    let cargo_fmt_status = cargo_fmt.status().expect("failed to run cargo fmt");
    if !cargo_fmt_status.success() {
        anyhow::bail!(
            "cargo fmt on {} returned status code {:?}",
            path_filename.display(),
            cargo_fmt_status.code()
        );
    }

    Ok(())
}

fn format_vstd(options: &VargoOptions, vargo_cmd: &VargoFmt) -> anyhow::Result<()> {
    if vargo_cmd.vstd_no_verusfmt {
        return Ok(());
    }

    let verusfmt_path: PathBuf = std::env::var("VARGO_VERUSFMT_PATH")
        .unwrap_or("verusfmt".to_string())
        .into();

    let Some(verusfmt_version) = verusfmt_get_version(&verusfmt_path, options.vargo_verbose)?
    else {
        return Ok(());
    };
    verusfmt_check_version(verusfmt_version)?;

    info!("formatting vstd");

    let vstd_path = std::path::Path::new("vstd");
    let all_vstd_files = walkdir::WalkDir::new(vstd_path)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|x| x.path().extension() == Some(std::ffi::OsStr::new("rs")))
        .map(|x| x.path().to_owned())
        .collect::<Vec<_>>();

    let mut verusfmt = std::process::Command::new(&verusfmt_path);
    verusfmt.args(&vargo_cmd.rustfmt_args);
    verusfmt.args(all_vstd_files);
    log_command(&verusfmt, options.vargo_verbose);
    verusfmt
        .status()
        .context("failed to run verusfmt on vstd")
        .and_then(|status| {
            if status.success() {
                Ok(())
            } else if let Some(code) = status.code() {
                Err(anyhow::anyhow!("`verusfmt` returned status code {code}"))
            } else {
                Err(anyhow::anyhow!("`verusfmt` was terminated by a signal"))
            }
        })
}

fn verusfmt_get_version(
    verusfmt_path: impl AsRef<Path>,
    verbose: bool,
) -> anyhow::Result<Option<(u64, u64, u64)>> {
    let verusfmt_path = verusfmt_path.as_ref();
    let mut cmd = std::process::Command::new(verusfmt_path);
    cmd.arg("--version");
    log_command(&cmd, verbose);

    let version_output = match cmd.output() {
        Ok(output) => output,
        Err(err) => match err.kind() {
            std::io::ErrorKind::NotFound => {
                warning!(
                        "cannot execute verusfmt, refer to https://github.com/verus-lang/verusfmt/blob/main/README.md#installing-and-using-verusfmt for installation instructions\nvstd will not be formatted"
                    );
                return Ok(None);
            }
            _ => return Err(err).context("cannot execute verusfmt"),
        },
    };

    if !version_output.status.success() {
        if let Some(code) = version_output.status.code() {
            return Err(anyhow::anyhow!("`verusfmt` returned status code {}", code));
        } else {
            return Err(anyhow::anyhow!("`verusfmt` was terminated by a signal",));
        }
    }

    let verusfmt_version_stdout =
        String::from_utf8(version_output.stdout).context("invalid output from verusfmt")?;

    let verusfmt_version_re =
        Regex::new(r"^verusfmt ([0-9]+)\.([0-9]+)\.([0-9]+)(?:-.*)?\n$").unwrap();
    let verusfmt_version = verusfmt_version_re
        .captures(&verusfmt_version_stdout)
        .ok_or_else(|| anyhow::anyhow!("invalid output from verusfmt"))?
        .extract::<3>()
        .1
        .iter()
        .map(|v| v.parse::<u64>().unwrap())
        .collect::<Vec<u64>>();

    Ok(Some((
        verusfmt_version[0],
        verusfmt_version[1],
        verusfmt_version[2],
    )))
}

fn verusfmt_check_version(verusfmt_version: (u64, u64, u64)) -> anyhow::Result<()> {
    if MINIMUM_VERUSFMT_VERSION > verusfmt_version {
        Err(anyhow::anyhow!(
                    "expected `verusfmt` version to be at least {}.{}.{}, found {}.{}.{}; refer to https://github.com/verus-lang/verusfmt/blob/main/README.md#installing-and-using-verusfmt for installation instructions",
                    MINIMUM_VERUSFMT_VERSION.0,
                    MINIMUM_VERUSFMT_VERSION.1,
                    MINIMUM_VERUSFMT_VERSION.2,
                    verusfmt_version.0,
                    verusfmt_version.1,
                    verusfmt_version.2
                ))
    } else {
        Ok(())
    }
}
