use std::collections::BTreeSet as Set;
use std::env;
use std::path::PathBuf;
use std::process::Command;

use anyhow::{Result, bail};
use cargo_metadata::{Metadata, PackageId};

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

pub fn make_verus_plan(
    subcommand: &str,
    metadata: Metadata,
    verify_deps: bool,
    cargo_options: &CargoOptions,
    verus_args: &[String],
    warn_if_nothing_verified: bool,
) -> Result<(Command, bool)> {
    let metadata_index = MetadataIndex::new(&metadata)?;

    let (included_packages, _excluded_packages) =
        cargo_options.workspace.partition_packages(&metadata);

    let root_packages: Set<PackageId> =
        included_packages.iter().map(|package| package.id.clone()).collect();
    let all_packages = metadata_index.get_transitive_closure(root_packages.clone());

    let packages_to_process = &all_packages;
    let packages_to_verify = if verify_deps { &all_packages } else { &root_packages };

    let cargo_args = {
        let for_cargo_metadata = false;
        make_cargo_args(cargo_options, for_cargo_metadata)
    };

    let cfg = CargoCommandConfig {
        subcommand,
        metadata_index: &metadata_index,
        packages_to_process,
        packages_to_verify,
        cargo_args: &cargo_args,
        verus_args: &verus_args,
        warn_if_nothing_verified,
    };

    let (command, verified_something) = make_cargo_command(cfg)?;

    let warn_nothing_verified = warn_if_nothing_verified && !verified_something;

    Ok((command, warn_nothing_verified))
}

pub fn make_cargo_args(opts: &CargoOptions, for_cargo_metadata: bool) -> Vec<String> {
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

pub struct CargoCommandConfig<'a> {
    subcommand: &'a str,
    metadata_index: &'a MetadataIndex<'a>,
    packages_to_process: &'a Set<PackageId>,
    packages_to_verify: &'a Set<PackageId>,
    cargo_args: &'a [String],
    verus_args: &'a [String],
    warn_if_nothing_verified: bool,
}

fn make_cargo_command(cfg: CargoCommandConfig) -> Result<(Command, bool)> {
    let mut common_verus_driver_args: Vec<String> =
        vec!["--VIA-CARGO".to_owned(), "compile-when-not-primary-package".to_owned()];

    if !cfg.warn_if_nothing_verified {
        common_verus_driver_args.extend_from_slice(&[
            "--VIA-CARGO".to_owned(),
            "compile-when-primary-package".to_owned(),
        ]);
    }

    common_verus_driver_args.extend(cfg.verus_args.iter().cloned());

    // TODO: use the "+ ... toolchain" argument?
    let mut cmd = Command::new(env::var("CARGO").unwrap_or("cargo".into()));

    cmd.arg(cfg.subcommand.to_owned()).args(cfg.cargo_args);

    cmd.env("RUSTC_WRAPPER", get_verus_driver_path());

    cmd.env(VERUS_DRIVER_VIA_CARGO, "1");

    // See https://github.com/rust-lang/cargo/blob/94aa7fb1321545bbe922a87cb11f5f4559e3be63/src/cargo/core/compiler/fingerprint/mod.rs#L71
    cmd.env("__CARGO_DEFAULT_LIB_METADATA", "verus");

    let common_verus_driver_args = pack_verus_driver_args_for_env(common_verus_driver_args.iter());

    if !common_verus_driver_args.is_empty() {
        cmd.env(VERUS_DRIVER_ARGS, common_verus_driver_args);
    }

    let mut verified_something = false;
    for pkg_id in cfg.packages_to_process {
        let no_verify = !cfg.packages_to_verify.contains(&pkg_id);

        let entry = cfg.metadata_index.get(pkg_id);
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
            if !verus_metadata.is_vstd && !no_verify {
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

            if no_verify {
                verus_driver_args_for_package.push("--no-verify".to_owned());
            }

            for dep in entry.deps() {
                if cfg.metadata_index.get(&dep.pkg).verus_metadata().verify {
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
