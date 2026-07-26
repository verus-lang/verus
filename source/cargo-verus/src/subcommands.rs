use std::collections::{BTreeMap as Map, BTreeSet as Set};
use std::env;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, anyhow, bail};
use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};
use cargo_metadata::{FeatureName, Metadata, PackageId};
use clap::ValueEnum;
use colored::Colorize;

use crate::ExecutionPlan;
use crate::cli::{CargoOptions, VerifyCommand, VerusArgFwdSelector};
use crate::metadata::{MetadataIndex, fetch_metadata, make_package_id};
use crate::toolchains::{self, TOOLCHAINS, is_matching_known_and_used};

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
vstd = "=0.0.0-2026-07-12-0122"

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

pub fn list_toolchains() -> Result<ExitCode> {
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    for toolchain in TOOLCHAINS.iter() {
        writeln!(&mut out, "verus = {:?}", toolchain.verus)?;
        writeln!(&mut out, "vstd = {}", toolchain.vstd)?;
        writeln!(&mut out, "z3 = {:?}", toolchain.z3)?;
        writeln!(&mut out)?;
    }
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

pub fn plan_cargo_run(cfg: VerusConfig) -> Result<ExecutionPlan> {
    let fwd_verus_args_to = cfg.options.fwd_verus_args_to.expect("fwd_verus_args_to must be set");

    //////////////////////////////////////////////////
    // Phase 1: fetch metadata via `cargo metadata` //
    //////////////////////////////////////////////////
    let metadata_args = {
        let for_cargo_metadata = true;
        make_cargo_args(&cfg.options.cargo_opts, for_cargo_metadata, cfg.options.verbosity)
    };
    let metadata = fetch_metadata(metadata_args, cfg.current_dir.clone())?;
    let metadata_index = MetadataIndex::new(&metadata)?;

    let (included_packages, _excluded_packages) =
        cfg.options.cargo_opts.workspace.partition_packages(&metadata);

    let root_packages: Set<PackageId> =
        included_packages.iter().map(|package| package.id.clone()).collect();
    let all_packages = metadata_index.get_transitive_closure(root_packages.clone());
    let dep_packages: Set<PackageId> = all_packages.difference(&root_packages).cloned().collect();

    if cfg.subcommand == "build"
        && root_packages.len() == 1
        && let Some(only_primary_vstd) = root_packages
            .iter()
            .find(|package_id| metadata_index.get(package_id).verus_metadata.is_vstd)
            .cloned()
    {
        // When the only primary package to build is `vstd`, switch to a specialized code path.
        let build_vstd_plan = make_vstd_build_plan(
            &cfg.current_dir,
            &cfg.options.cargo_opts,
            &only_primary_vstd,
            &metadata,
            &metadata_index,
            &cfg.options.verus_args,
        )?;
        return Ok(ExecutionPlan::BuildVstd(build_vstd_plan));
    };

    let packages_to_process = &all_packages;
    let packages_to_verify = if cfg.verify_deps { &all_packages } else { &root_packages };

    let fwd_verus_args_packages = match fwd_verus_args_to {
        VerusArgFwdSelector::All => &all_packages,
        VerusArgFwdSelector::Roots => &root_packages,
        VerusArgFwdSelector::Deps => &dep_packages,
    };

    if cfg.options.check_toolchain {
        if cfg.options.verbosity > 0 {
            println!("Checking toolchain components...");
        }

        let vstd_metadata = metadata_index.collect_vstd_metadata(packages_to_verify);
        let verus_version = get_verus_driver_version()?;

        if cfg.options.verbosity > 0 {
            println!("verus version: {verus_version:?}");
            println!("`vstd` instances:");
            for vstd in &vstd_metadata {
                println!("version = {:?}", vstd.version.to_string());
                println!("source = {:?}", vstd.source);
                println!();
            }
        }

        for used_vstd in &vstd_metadata {
            let is_compatible = toolchains::TOOLCHAINS.iter().any(|toolchain| {
                toolchain.verus == verus_version
                    && is_matching_known_and_used(&toolchain.vstd, used_vstd)
            });
            if !is_compatible {
                bail!(
                    "Components are incompatible:\n\
                    * verus = {verus_version}\n\
                    * vstd = {used_vstd:?}\n"
                );
            }
        }
    }

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
        make_cargo_args(&options, for_cargo_metadata, cfg.options.verbosity)
    };

    let mut common_verus_driver_args: Vec<String> =
        vec!["--VIA-CARGO".to_owned(), "compile-when-not-primary-package".to_owned()];

    if cfg.compile_primary {
        common_verus_driver_args.extend_from_slice(&[
            "--VIA-CARGO".to_owned(),
            "compile-when-primary-package".to_owned(),
        ]);
    }
    if cfg.options.verbosity >= 2 {
        common_verus_driver_args.push("-v".to_owned());
        eprintln!("verbosity level >= 2; forwarding 1 `-v` to Verus");
    } else if cfg.options.verbosity > 0 {
        eprintln!("verbosity level = 1; keeping Verus non-verbose");
    }

    let cargo_run_plan = make_cargo_plan(
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

    if cfg.options.verbosity > 0 {
        let command = cargo_run_plan.to_command();
        eprintln!(
            "forwarding Verus args to crates: <{}>",
            fwd_verus_args_to.to_possible_value().expect("arg value").get_name(),
        );
        eprintln!("running cargo command:\n{command:?}");
    }

    if cfg.warn_if_nothing_verified && !cargo_run_plan.verified_something {
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

    Ok(ExecutionPlan::RunCargo(cargo_run_plan))
}

fn make_cargo_args(opts: &CargoOptions, for_cargo_metadata: bool, verbosity: u8) -> Vec<String> {
    let mut args = vec![];

    for _ in 1..verbosity {
        args.push("-v".to_owned());
    }
    if verbosity > 0 {
        eprintln!(
            "verbosity level = {verbosity}; forwarding {} `-v` arg(s) to Cargo",
            verbosity - 1,
        );
    }

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
        if opts.release {
            args.push("--release".to_owned());
        }

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
        let package = entry.package;

        let package_id =
            make_package_id(&package.name, package.version.to_string(), &package.manifest_path);

        let verus_metadata = &entry.verus_metadata;

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

            for import_name in metadata_index.transitive_verified_import_names(pkg_id) {
                verus_driver_args_for_package.extend_from_slice(&[
                    "--VIA-CARGO".to_owned(),
                    format!("import-dep-if-present={import_name}"),
                ]);
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

pub struct VstdBuildPlan {
    pub current_dir: PathBuf,
    pub target_dir: Utf8PathBuf,
    pub cargo_options: CargoOptions,
    pub vstd_manifest: Utf8PathBuf,
    pub vstd_features: Set<String>,
    pub verus_builtin_manifest: Utf8PathBuf,
    pub verus_builtin_macros_manifest: Utf8PathBuf,
    pub verus_state_machines_macros_manifest: Utf8PathBuf,
}

fn make_vstd_build_plan(
    current_dir: &Path,
    cargo_options: &CargoOptions,
    vstd_id: &PackageId,
    metadata: &Metadata,
    metadata_index: &MetadataIndex,
    // Args forwarded to Verus
    _fwd_verus_args: &[String],
) -> Result<VstdBuildPlan> {
    use cargo_metadata::NodeDep;
    use std::collections::BTreeMap;

    let vstd_metadata = metadata_index.get(vstd_id);
    let vstd_manifest = vstd_metadata.package.manifest_path.clone();

    fn find_dep_by_name<'a>(
        deps: &BTreeMap<&'a PackageId, &'a NodeDep>,
        name: &str,
    ) -> &'a PackageId {
        let (package_id, _): (&&PackageId, _) =
            deps.iter().find(|(_, dep)| dep.name == name).expect(&format!("find dep `{name}`"));
        package_id
    }

    let verus_builtin_id = find_dep_by_name(&vstd_metadata.deps, "verus_builtin");
    let verus_builtin_manifest = metadata_index.get(verus_builtin_id).package.manifest_path.clone();

    let verus_builtin_macros_id = find_dep_by_name(&vstd_metadata.deps, "verus_builtin_macros");
    let verus_builtin_macros_manifest =
        metadata_index.get(verus_builtin_macros_id).package.manifest_path.clone();

    let verus_state_machines_macros_id =
        find_dep_by_name(&vstd_metadata.deps, "verus_state_machines_macros");
    let verus_state_machines_macros_manifest =
        metadata_index.get(verus_state_machines_macros_id).package.manifest_path.clone();

    // Resolve the features of `vstd` that are on.
    let mut vstd_features: Set<String> =
        vstd_metadata.features.iter().map(FeatureName::to_string).collect();
    vstd_features.insert("nonzero_internals".into());

    // Sanitize Cargo options.
    let mut cargo_options = cargo_options.clone();
    cargo_options.manifest.manifest_path = None;
    cargo_options.features.all_features = false;
    cargo_options.features.no_default_features = false;
    cargo_options.features.features.clear();
    cargo_options.workspace.package.clear();
    cargo_options.workspace.workspace = false;
    cargo_options.workspace.all = false;
    cargo_options.workspace.exclude.clear();
    if cargo_options.target_dir.is_none() {
        cargo_options.target_dir = None;
    }

    Ok(VstdBuildPlan {
        current_dir: current_dir.to_owned(),
        target_dir: metadata.target_directory.clone(),
        cargo_options,
        vstd_manifest,
        vstd_features,
        verus_builtin_manifest,
        verus_builtin_macros_manifest,
        verus_state_machines_macros_manifest,
    })
}

// Special code path for a build where the *only* primary package is `vstd` itself.
pub fn build_vstd(plan: &VstdBuildPlan) -> Result<ExitCode> {
    let dependency_args = make_cargo_args(&plan.cargo_options, false, 0);
    let cargo = env::var("CARGO").unwrap_or_else(|_| "cargo".to_owned());

    let dispatch_build_dep = |name: &str, manifest_path: &Utf8Path| -> Result<ExitCode> {
        let mut build_command = Command::new(&cargo);
        build_command
            .current_dir(&plan.current_dir)
            .arg("build")
            .args(["--manifest-path", manifest_path.as_str()])
            .args(&dependency_args);
        let build_status = build_command
            .spawn()
            .with_context(|| format!("building `{name}`"))?
            .wait()
            .with_context(|| format!("waiting to build `{name}`"))?;
        if !build_status.success() {
            bail!("Command {build_command:?} failed");
        };
        match build_status.code() {
            Some(code) => u8::try_from(code).map(From::from).map_err(|_| {
                anyhow!("Command {build_command:?} returned an odd exit code: {code}")
            }),
            None => bail!("Command {build_command:?} was terminated by a signal: {build_status}"),
        }
    };

    let profile = if plan.cargo_options.release { "release" } else { "debug" };
    let output_dir = plan.target_dir.join(profile);

    let mut externs = Map::<&str, PathBuf>::new();

    dispatch_build_dep("verus_builtin", &plan.verus_builtin_manifest)?;
    let verus_builtin_rlib = output_dir.join("libverus_builtin.rlib").into_std_path_buf();
    externs.insert("verus_builtin", verus_builtin_rlib);

    dispatch_build_dep("verus_builtin_macros", &plan.verus_builtin_macros_manifest)?;
    let verus_builtin_macros_dylib = output_dir
        .join(format!("libverus_builtin_macros.{}", std::env::consts::DLL_EXTENSION))
        .into_std_path_buf();
    externs.insert("verus_builtin_macros", verus_builtin_macros_dylib);

    dispatch_build_dep("verus_state_machines_macros", &plan.verus_state_machines_macros_manifest)?;
    let verus_state_machines_macros_dylib = output_dir
        .join(format!("libverus_state_machines_macros.{}", std::env::consts::DLL_EXTENSION))
        .into_std_path_buf();
    externs.insert("verus_state_machines_macros", verus_state_machines_macros_dylib);

    let vstd_source = plan.vstd_manifest.with_file_name("vstd.rs");
    let cargo_verus_path =
        env::current_exe().context("getting the current cargo-verus executable path")?;
    let rust_verify_path = cargo_verus_path
        .with_file_name("rust_verify")
        .with_extension(std::env::consts::EXE_EXTENSION);

    let mut build_command = Command::new(rust_verify_path);
    build_command
        .current_dir(&plan.current_dir)
        .env("RUST_MIN_STACK", (10 * 1024 * 1024).to_string())
        .env("VSTD_KIND", "IsVstd")
        .args(["--internal-test-mode", "--crate-type=lib", "--is-vstd", "--compile"])
        .args(["--multiple-errors", "2"])
        .args(["--out-dir", output_dir.as_str()])
        .args(["--export", output_dir.join("vstd.vir").as_str()]);
    if plan.cargo_options.release {
        build_command.args(["-C", "opt-level=3"]);
    }
    for (name, path) in externs {
        build_command.args(["--extern", &format!("{name}={}", path.display())]);
    }
    for feature in &plan.vstd_features {
        build_command.args(["--cfg", &format!("feature={feature:?}")]);
    }
    build_command.arg(vstd_source);

    let build_status = build_command
        .spawn()
        .context("running `rust_verify` to build `vstd`")?
        .wait()
        .context("waiting for `rust_verify` to build `vstd`")?;
    if !build_status.success() {
        bail!("Command {build_command:?} failed");
    };
    match build_status.code() {
        Some(code) => u8::try_from(code)
            .map(ExitCode::from)
            .map_err(|_| anyhow!("Command {build_command:?} returned an odd exit code: {code}")),
        None => bail!("Command {build_command:?} was terminated by a signal: {build_status}"),
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

/// Run `verus --version` and capture its output.
fn get_verus_driver_version() -> Result<String> {
    let command = get_verus_driver_path();
    let output = Command::new(&command)
        .arg("--version")
        .output()
        .context(format!("running `{} --version`", command.display()))?;

    if !output.status.success() {
        bail!(
            "`{} --version` failed with status {}.\n\
            stdout:\n{}\n\
            stderr:\n{}",
            command.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
    }

    let stdout = String::from_utf8(output.stdout)
        .context(format!("`{} --version` produced non-UTF-8 stdout", command.display()))?;

    stdout.lines().find_map(|line| line.strip_prefix("  Version: ").map(ToOwned::to_owned)).context(
        format!("Failed to parse version from `{}` output:\n{}", command.display(), stdout),
    )
}
