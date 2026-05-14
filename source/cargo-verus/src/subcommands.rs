use std::collections::{BTreeMap as Map, BTreeSet as Set};
use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, anyhow, bail};
use cargo_metadata::PackageId;
use clap::ValueEnum;
use colored::Colorize;

use crate::cli::{CargoOptions, VerifyCommand, VerusArgFwdSelector};
use crate::metadata::{MetadataIndex, fetch_metadata, make_package_id};

pub const CARGO_DEFAULT_LIB_METADATA: &str = "__CARGO_DEFAULT_LIB_METADATA";

pub const RUSTC_WRAPPER: &str = "RUSTC_WRAPPER";

pub const VERUS_DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
pub const VERUS_DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
pub const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
pub const VERUS_DRIVER_IS_BUILTIN: &str = " __VERUS_DRIVER_IS_BUILTIN_";
pub const VERUS_DRIVER_IS_BUILTIN_MACROS: &str = " __VERUS_DRIVER_IS_BUILTIN_MACROS_";
pub const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";
pub const VERUS_DRIVER_VIA_CARGO: &str = "__VERUS_DRIVER_VIA_CARGO__";

pub struct NewCreationPlan {
    pub current_dir: PathBuf,
    pub name: String,
    pub is_bin: bool,
}

pub fn create_new_project(creation_plan: &NewCreationPlan) -> Result<ExitCode> {
    let NewCreationPlan { current_dir, name, is_bin } = creation_plan;

    let (src_rs, src_rs_data) = if *is_bin {
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
vstd = "=0.0.0-2026-05-10-0145"

[package.metadata.verus]
verify = true

[lints.rust]
# Verus supports ghost code, code that is used for proofs but erased during compilation.
# This means that ghost items that are imported via `use` will not exist during a normal
# `cargo build`, leading to compilation errors. These errors can be prevented by guarding the
# use statements with the feature flag `verus_only`, which Verus turns on during
# verification.
#
# WARNING: this flag should only be used on import statements and setting config attributes,
# see the documentation (https://verus-lang.github.io/verus/guide/erasure.html) for more details.
#
# This lint suppression prevents cargo from complaining about the
# `verus_only` feature flag being undeclared.
unexpected_cfgs = {{ level = "warn", check-cfg = [
  'cfg(verus_only)',
] }}"#
    );

    let project_dir = current_dir.join(name);
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

    Ok(ExitCode::SUCCESS)
}

pub struct VerusConfig {
    pub current_dir: PathBuf,
    pub subcommand: &'static str,
    pub options: VerifyCommand,
    pub compile_primary: bool,
    pub verify_deps: bool,
    pub warn_if_nothing_verified: bool,
}

pub fn plan_cargo_run(cfg: VerusConfig) -> Result<CargoRunPlan> {
    let fwd_verus_args_to = cfg.options.fwd_verus_args_to.expect("fwd_verus_args_to must be set");

    //////////////////////////////////////////////////
    // Phase 1: fetch metadata via `cargo metadata` //
    //////////////////////////////////////////////////
    let metadata_args = {
        let for_cargo_metadata = true;
        make_cargo_args(&cfg.options.cargo_opts, for_cargo_metadata)
    };
    let metadata = fetch_metadata(metadata_args, cfg.current_dir.clone())?;
    let metadata_index = MetadataIndex::new(&metadata)?;

    let (included_packages, _excluded_packages) =
        cfg.options.cargo_opts.workspace.partition_packages(&metadata);

    let root_packages: Set<PackageId> =
        included_packages.iter().map(|package| package.id.clone()).collect();
    let all_packages = metadata_index.get_transitive_closure(root_packages.clone());
    let dep_packages: Set<PackageId> = all_packages.difference(&root_packages).cloned().collect();

    let packages_to_process = &all_packages;
    let packages_to_verify = if cfg.verify_deps { &all_packages } else { &root_packages };

    let fwd_verus_args_packages = match fwd_verus_args_to {
        VerusArgFwdSelector::All => &all_packages,
        VerusArgFwdSelector::Roots => &root_packages,
        VerusArgFwdSelector::Deps => &dep_packages,
    };

    /////////////////////////////////////////////////////////
    // Phase 2: plan to run Verus via `cargo {subcommand}` //
    /////////////////////////////////////////////////////////

    let cargo_args = {
        let mut options = cfg.options.cargo_opts;
        if !cfg.verify_deps {
            // Ensure that partially verified artifacts are separated from complete results
            let target_dir =
                options.target_dir.unwrap_or(metadata.target_directory.clone().into_std_path_buf());
            options.target_dir = Some(target_dir.join("verus-partial"));
        }

        let for_cargo_metadata = false;
        make_cargo_args(&options, for_cargo_metadata)
    };

    let mut common_verus_driver_args: Vec<String> =
        vec!["--VIA-CARGO".to_owned(), "compile-when-not-primary-package".to_owned()];

    if cfg.compile_primary {
        common_verus_driver_args.extend_from_slice(&[
            "--VIA-CARGO".to_owned(),
            "compile-when-primary-package".to_owned(),
        ]);
    }

    let plan = make_cargo_plan(
        cfg.current_dir,
        cfg.subcommand,
        cargo_args,
        common_verus_driver_args,
        &metadata_index,
        packages_to_process,
        packages_to_verify,
        &cfg.options.verus_args,
        fwd_verus_args_packages,
    )?;

    if cfg.options.verbose {
        let command = plan.to_command();
        eprintln!(
            "forwarding Verus args to crates: <{}>",
            fwd_verus_args_to.to_possible_value().expect("arg value").get_name(),
        );
        eprintln!("running cargo command:\n{command:?}");
    }

    if cfg.warn_if_nothing_verified && !plan.verified_something {
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

    Ok(plan)
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

    if !for_cargo_metadata {
        if let Some(path) = &opts.target_dir {
            args.push("--target-dir".to_owned());
            args.push(path.to_string_lossy().into_owned());
        }

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

        args.extend(opts.cargo_args.iter().cloned());
    }

    args
}

#[derive(Clone, Debug)]
pub struct CargoRunPlan {
    pub current_dir: PathBuf,
    pub args: Vec<String>,
    pub env: Map<String, String>,
    pub verified_something: bool,
}

impl CargoRunPlan {
    fn to_command(&self) -> Command {
        let mut command = Command::new(env::var("CARGO").unwrap_or("cargo".into()));
        command.current_dir(&self.current_dir);
        command.args(&self.args);
        for (key, value) in &self.env {
            command.env(key, value);
        }
        command
    }
}

fn make_cargo_plan(
    current_dir: PathBuf,
    subcommand: &'static str,
    mut cargo_args: Vec<String>,
    common_verus_driver_args: Vec<String>,
    metadata_index: &MetadataIndex,
    packages_to_process: &Set<PackageId>,
    packages_to_verify: &Set<PackageId>,
    // Args forwarded to Verus
    fwd_verus_args: &[String],
    // Packages to receive forwarded Verus args
    fwd_verus_args_packages: &Set<PackageId>,
) -> Result<CargoRunPlan> {
    let mut env_overrides = Map::new();
    env_overrides
        .insert(RUSTC_WRAPPER.to_owned(), get_verus_driver_path().to_string_lossy().into_owned());
    env_overrides.insert(VERUS_DRIVER_VIA_CARGO.to_owned(), "1".to_owned());
    // See https://github.com/rust-lang/cargo/blob/94aa7fb1321545bbe922a87cb11f5f4559e3be63/src/cargo/core/compiler/fingerprint/mod.rs#L71
    env_overrides.insert(CARGO_DEFAULT_LIB_METADATA.to_owned(), "verus".to_owned());

    let common_verus_driver_args = pack_verus_driver_args_for_env(common_verus_driver_args.iter());

    if !common_verus_driver_args.is_empty() {
        env_overrides.insert(VERUS_DRIVER_ARGS.to_owned(), common_verus_driver_args);
    }

    let mut verified_something = false;
    for pkg_id in packages_to_process {
        let no_verify = !packages_to_verify.contains(&pkg_id);
        let receives_fwd_verus_args = fwd_verus_args_packages.contains(&pkg_id);

        let entry = metadata_index.get(pkg_id);
        let package = entry.package();

        let package_id =
            make_package_id(&package.name, package.version.to_string(), &package.manifest_path);

        let verus_metadata = entry.verus_metadata();

        // The is_builtin, is_builtin_macro, and verify fields are passed as env vars as they
        // are relevant for crates which are skipped by Verus. In such cases, the driver avoids
        // depending on __VERUS_DRIVER_ARGS__ to prevent unecessary rebuilds when its value
        // changes.

        if verus_metadata.is_builtin {
            env_overrides.insert(format!("{VERUS_DRIVER_IS_BUILTIN}{package_id}"), "1".to_owned());
        }

        if verus_metadata.is_builtin_macros {
            env_overrides
                .insert(format!("{VERUS_DRIVER_IS_BUILTIN_MACROS}{package_id}"), "1".to_owned());
        }

        if verus_metadata.verify {
            // Any project using Verus may pull in vstd, which has a Cargo.toml file verify=true
            if !verus_metadata.is_vstd && !no_verify {
                verified_something = true;
            }
            env_overrides.insert(format!("{VERUS_DRIVER_VERIFY}{package_id}"), "1".to_owned());

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
                if metadata_index.get(&dep.pkg).verus_metadata().verify {
                    verus_driver_args_for_package.extend_from_slice(&[
                        "--VIA-CARGO".to_owned(),
                        format!("import-dep-if-present={}", dep.name),
                    ]);
                }
            }

            // If the package has a lib target *and* a non-lib target, like a test or example,
            // add the lib as a dependency so the auxiliary target can see it. This adds the lib
            // as a dep to itself, but it will not be present in the externs, so will be ignored.
            if let Some(lib_target) = package.targets.iter().find(|t| t.is_lib()) {
                if package.targets.iter().any(|t| !t.is_lib()) {
                    verus_driver_args_for_package.extend_from_slice(&[
                        "--VIA-CARGO".to_owned(),
                        format!("import-dep-if-present={}", lib_target.name),
                    ])
                }
            }

            if receives_fwd_verus_args {
                verus_driver_args_for_package.extend(fwd_verus_args.iter().cloned());
            }

            if !verus_driver_args_for_package.is_empty() {
                env_overrides.insert(
                    format!("{VERUS_DRIVER_ARGS_FOR}{package_id}"),
                    pack_verus_driver_args_for_env(verus_driver_args_for_package.iter()),
                );
            }
        }
    }

    let mut args = vec![subcommand.to_owned()];
    args.append(&mut cargo_args);

    Ok(CargoRunPlan { current_dir, args, env: env_overrides, verified_something })
}

pub fn run_cargo(plan: &CargoRunPlan) -> Result<ExitCode> {
    // TODO: use the "+ ... toolchain" argument?
    let mut command = plan.to_command();

    let exit_status = command
        .spawn()
        .context("Failed to spawn cargo")?
        .wait()
        .context("Failed to wait for cargo")?;

    match exit_status.code() {
        Some(code) => u8::try_from(code)
            .map(From::from)
            .map_err(|_| anyhow!("Command {command:?} terminated with an odd exit code: {code}")),
        None => bail!("Command {command:?} was terminated by a signal: {exit_status}"),
    }
}

fn pack_verus_driver_args_for_env(args: impl Iterator<Item = impl AsRef<str>>) -> String {
    args.flat_map(|arg| [VERUS_DRIVER_ARGS_SEP.to_owned(), arg.as_ref().to_owned()]).collect()
}

fn get_verus_driver_path() -> PathBuf {
    let mut path =
        env::current_exe().expect("current executable path invalid").with_file_name("verus");

    if cfg!(windows) {
        path.set_extension("exe");
    }

    path
}
