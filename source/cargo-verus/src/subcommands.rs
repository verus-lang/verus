use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, anyhow, bail};
use colored::Colorize;

use crate::cli::CargoOptions;
use crate::metadata::{MetadataIndex, fetch_metadata, make_package_id};

pub const VERUS_DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
pub const VERUS_DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
pub const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
pub const VERUS_DRIVER_IS_BUILTIN: &str = " __VERUS_DRIVER_IS_BUILTIN_";
pub const VERUS_DRIVER_IS_BUILTIN_MACROS: &str = " __VERUS_DRIVER_IS_BUILTIN_MACROS_";
pub const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";
pub const VERUS_DRIVER_VIA_CARGO: &str = "__VERUS_DRIVER_VIA_CARGO__";

pub fn create_new_project(name: &str, is_bin: bool) -> Result<()> {
    let (src_rs, src_rs_data) = if is_bin {
        (
            "main.rs",
            r#"
use vstd::prelude::*;

verus! {

fn main() {
    assert(1 == 0 + 1);
}

} // verus!
"#,
        )
    } else {
        (
            "lib.rs",
            r#"
use vstd::prelude::*;

verus! {

fn foo() {
    assert(1 == 0 + 1);
}

} // verus!
"#,
        )
    };

    let gitignore_data = "/target";
    let cargo_toml_data = format!(
        r#"
[package]
name = "{name}"
version = "0.1.0"
edition = "2021"

[dependencies]
vstd = "=0.0.0-2026-01-11-0057"

[package.metadata.verus]
verify = true
"#
    );

    let project_dir = PathBuf::from(name);
    if project_dir.exists() {
        bail!("Directory `{}` already exists", name);
    }

    std::fs::create_dir(&project_dir)?;
    std::fs::create_dir(project_dir.join("src"))?;
    std::fs::write(project_dir.join(".gitignore"), gitignore_data.trim_start())?;
    std::fs::write(project_dir.join("Cargo.toml"), cargo_toml_data.trim_start())?;
    std::fs::write(project_dir.join("src").join(src_rs), src_rs_data.trim_start())?;
    let git_init = Command::new("git")
        .current_dir(project_dir)
        .arg("init")
        .stdout(std::process::Stdio::null())
        .status()?;
    assert!(git_init.success());

    println!("Created new Verus project at {name}");

    Ok(())
}

pub fn run_cargo(
    subcommand: &str,
    cargo_options: &CargoOptions,
    verus_args: &[String],
    warn_if_nothing_verified: bool,
) -> Result<ExitCode> {
    let cargo_args = make_cargo_args(cargo_options, false);
    let mut common_verus_driver_args: Vec<String> =
        vec!["--VIA-CARGO".to_owned(), "compile-when-not-primary-package".to_owned()];

    if !warn_if_nothing_verified {
        common_verus_driver_args.extend_from_slice(&[
            "--VIA-CARGO".to_owned(),
            "compile-when-primary-package".to_owned(),
        ]);
    }

    let metadata_args = make_cargo_args(cargo_options, true);
    let metadata = fetch_metadata(&metadata_args)?;

    common_verus_driver_args.extend(verus_args.iter().cloned());
    let (mut command, verified_something) =
        make_cargo_command(subcommand, &cargo_args, common_verus_driver_args, &metadata)?;

    let exit_status = command
        .spawn()
        .context("Failed to spawn cargo")?
        .wait()
        .context("Failed to wait for cargo")?;

    if warn_if_nothing_verified && !verified_something {
        eprint!(
            "{}",
            "\
WARNING: You asked for verification, but cargo did not find any crates that opted into verification.
         If this is unexpected, try adding this entry to your Cargo.toml file:
            [package.metadata.verus]
            verify = true
"
            .red(),
        );
    }

    match exit_status.code() {
        Some(code) => u8::try_from(code)
            .map(From::from)
            .map_err(|_| anyhow!("Command {command:?} terminated with an odd exit code: {code}")),
        None => bail!("Command {command:?} was terminated by a signal: {exit_status}"),
    }
}

fn make_cargo_args(opts: &CargoOptions, for_cargo_metadata: bool) -> Vec<String> {
    let mut args = vec![];

    if opts.frozen {
        args.push("--frozen".to_owned());
    }

    if opts.locked {
        args.push("--locked".to_owned());
    }

    if opts.offline {
        args.push("--offline".to_owned());
    }

    for cfg in &opts.config {
        args.push("--config".to_owned());
        args.push(cfg.clone());
    }

    for flag in &opts.unstable_flags {
        args.push("-Z".to_owned());
        args.push(flag.clone());
    }

    if let Some(path) = &opts.manifest.manifest_path {
        args.push("--manifest-path".to_owned());
        args.push(path.to_string_lossy().into_owned());
    }

    if !for_cargo_metadata {
        for pkg in &opts.workspace.package {
            args.push("--package".to_owned());
            args.push(pkg.clone());
        }

        if opts.workspace.workspace {
            args.push("--workspace".to_owned());
        }

        if opts.workspace.all {
            args.push("--all".to_owned());
        }

        for exclude in &opts.workspace.exclude {
            args.push("--exclude".to_owned());
            args.push(exclude.clone());
        }

        if opts.features.all_features {
            args.push("--all-features".to_owned());
        }

        if opts.features.no_default_features {
            args.push("--no-default-features".to_owned());
        }

        if !opts.features.features.is_empty() {
            args.push("--features".to_owned());
            args.push(opts.features.features.join(" "));
        }

        args.extend(opts.cargo_args.iter().cloned());
    }

    args
}

fn make_cargo_command(
    subcommand: &str,
    cargo_args: &[String],
    common_verus_driver_args: Vec<String>,
    metadata: &cargo_metadata::Metadata,
) -> Result<(Command, bool)> {
    // TODO: use the "+ ... toolchain" argument?
    let mut cmd = Command::new(env::var("CARGO").unwrap_or("cargo".into()));

    cmd.arg(subcommand.to_owned()).args(cargo_args);

    cmd.env("RUSTC_WRAPPER", get_verus_driver_path());

    cmd.env(VERUS_DRIVER_VIA_CARGO, "1");

    // See https://github.com/rust-lang/cargo/blob/94aa7fb1321545bbe922a87cb11f5f4559e3be63/src/cargo/core/compiler/fingerprint/mod.rs#L71
    cmd.env("__CARGO_DEFAULT_LIB_METADATA", "verus");

    let common_verus_driver_args = pack_verus_driver_args_for_env(common_verus_driver_args.iter());

    if !common_verus_driver_args.is_empty() {
        cmd.env(VERUS_DRIVER_ARGS, common_verus_driver_args);
    }

    let metadata_index = MetadataIndex::new(metadata)?;

    let mut verified_something = false;
    for entry in metadata_index.entries() {
        let package = entry.package();

        let package_id =
            make_package_id(&package.name, package.version.to_string(), &package.manifest_path);

        let verus_metadata = entry.verus_metadata();

        // The is_builtin, is_builtin_macro, and verify fields are passed as env vars as they
        // are relevant for crates which are skipped by Verus. In such cases, the driver avoids
        // depending on __VERUS_DRIVER_ARGS__ to prevent unecessary rebuilds when its value
        // changes.

        if verus_metadata.is_builtin {
            cmd.env(format!("{VERUS_DRIVER_IS_BUILTIN}{package_id}"), "1");
        }

        if verus_metadata.is_builtin_macros {
            cmd.env(format!("{VERUS_DRIVER_IS_BUILTIN_MACROS}{package_id}"), "1");
        }

        if verus_metadata.verify {
            // Any project using Verus may pull in vstd, which has a Cargo.toml file verify=true
            if !verus_metadata.is_vstd {
                verified_something = true;
            }
            cmd.env(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1");

            let mut verus_driver_args_for_package = vec![];

            if verus_metadata.is_core {
                verus_driver_args_for_package.push("--is-core".to_owned());
            }

            if verus_metadata.is_vstd {
                verus_driver_args_for_package.push("--is-vstd".to_owned());
            }

            if verus_metadata.no_vstd {
                verus_driver_args_for_package.push("--no-vstd".to_owned());
            }

            for dep in entry.deps() {
                if metadata_index.get(&dep.pkg).verus_metadata().verify {
                    verus_driver_args_for_package.extend_from_slice(&[
                        "--VIA-CARGO".to_owned(),
                        format!("import-dep-if-present={}", dep.name),
                    ]);
                }
            }

            if !verus_driver_args_for_package.is_empty() {
                cmd.env(
                    format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
                    pack_verus_driver_args_for_env(verus_driver_args_for_package.iter()),
                );
            }
        }
    }

    Ok((cmd, verified_something))
}

fn pack_verus_driver_args_for_env(args: impl Iterator<Item = impl AsRef<str>>) -> String {
    args.map(|arg| [VERUS_DRIVER_ARGS_SEP.to_owned(), arg.as_ref().to_owned()]).flatten().collect()
}

fn get_verus_driver_path() -> PathBuf {
    let mut path =
        env::current_exe().expect("current executable path invalid").with_file_name("verus");

    if cfg!(windows) {
        path.set_extension("exe");
    }

    path
}
