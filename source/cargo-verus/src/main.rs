//
// Copyright (c) 2024 The Verus Contributors
// Copyright (c) 2014-2024 The Rust Project Developers
//
// SPDX-License-Identifier: MIT
//
// Derived, with significant modification, from:
// https://github.com/rust-lang/rust-clippy/blob/master/src/main.rs
//

use std::collections::BTreeMap;
use std::env;
use std::path::PathBuf;
use std::process::{Command, ExitCode};
use std::str;

use anyhow::{Context, Result, anyhow, bail};
use cargo_metadata::{Metadata, MetadataCommand, Package, PackageId};
use colored::Colorize;
use serde::Deserialize;
use sha2::{Digest, Sha256};

pub const VERUS_DRIVER_ARGS: &str = " __VERUS_DRIVER_ARGS__";
pub const VERUS_DRIVER_ARGS_FOR: &str = " __VERUS_DRIVER_ARGS_FOR_";
pub const VERUS_DRIVER_ARGS_SEP: &str = "__VERUS_DRIVER_ARGS_SEP__";
pub const VERUS_DRIVER_IS_BUILTIN: &str = " __VERUS_DRIVER_IS_BUILTIN_";
pub const VERUS_DRIVER_IS_BUILTIN_MACROS: &str = " __VERUS_DRIVER_IS_BUILTIN_MACROS_";
pub const VERUS_DRIVER_VERIFY: &str = "__VERUS_DRIVER_VERIFY_";
pub const VERUS_DRIVER_VIA_CARGO: &str = "__VERUS_DRIVER_VIA_CARGO__";

pub fn main() -> Result<ExitCode> {
    // Choose offset into args according to whether we are being run as `cargo-verus` or `cargo verus`.
    // (See https://doc.rust-lang.org/cargo/reference/external-tools.html#custom-subcommands)
    let run_as_cargo_subcommand = matches!(env::args().nth(1).as_deref(), Some("verus"));
    let args =
        env::args().skip(1 + if run_as_cargo_subcommand { 1 } else { 0 }).collect::<Vec<_>>();

    if args.len() == 0 || args.iter().any(|a| a == "--help" || a == "-h") {
        show_help();
        return Ok(ExitCode::SUCCESS);
    }

    for arg in args.iter() {
        match arg.as_str() {
            "--" => break,
            _ => {
                if arg == "--version" || arg == "-V" {
                    show_version();
                    return Ok(ExitCode::SUCCESS);
                }
            }
        }
    }

    process(&args)
}

fn new_project(args: &[String]) -> Result<()> {
    let mut args_iter = args.iter();
    assert_eq!(args_iter.next(), Some(&"new".into()));
    let template_type =
        args_iter.next().ok_or_else(|| anyhow!("Expected `--bin NAME` or `--lib NAME`"))?;
    let name = args_iter.next().ok_or_else(|| anyhow!("Expected `--bin NAME` or `--lib NAME`"))?;

    let (src_rs, src_rs_data) = match template_type.as_str() {
        "--bin" => (
            "main.rs",
            r#"
use vstd::prelude::*;

verus! {

fn main() {
    assert(1 == 0 + 1);
}

} // verus!
"#,
        ),
        "--lib" => (
            "lib.rs",
            r#"
use vstd::prelude::*;

verus! {

fn foo() {
    assert(1 == 0 + 1);
}

} // verus!
"#,
        ),
        _ => bail!("Expected `--bin` or `--lib`, found `{}`", template_type),
    };

    let gitignore_data = "/target";
    let cargo_toml_data = r#"
[package]
name = "NAME"
version = "0.1.0"
edition = "2021"

[dependencies]
vstd = "=0.0.0-2025-11-30-0053"

[package.metadata.verus]
verify = true
"#
    .replace("NAME", name);

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

fn show_help() {
    println!("{}", help_message());
}

fn show_version() {
    let version_info = rustc_tools_util::get_version_info!();
    println!("{version_info}");
}

fn process(args: &[String]) -> Result<ExitCode> {
    let cmd = VerusCmd::new(args)?;

    if let CargoSubcommand::Nop = cmd.cargo_subcommand {
        return Ok(ExitCode::SUCCESS);
    }

    let mut cmd = cmd.into_std_cmd()?;

    let exit_status =
        cmd.spawn().context("Failed to spawn cargo")?.wait().context("Failed to wait for cargo")?;

    match exit_status.code() {
        Some(code) => u8::try_from(code)
            .map(From::from)
            .map_err(|_| anyhow!("Command {cmd:?} terminated with an odd exit code: {code}")),
        None => bail!("Command {cmd:?} was terminated by a signal: {exit_status}"),
    }
}

struct VerusCmd {
    cargo_subcommand: CargoSubcommand,
    cargo_args: Vec<String>,
    common_verus_driver_args: Vec<String>,
    verify: bool,
}

enum CargoSubcommand {
    Build,
    Check,
    /// Handled separately, no specific cargo subcommand needed
    Nop,
}

impl CargoSubcommand {
    fn to_arg(&self) -> &str {
        match self {
            Self::Build => "build",
            Self::Check => "check",
            Self::Nop => unreachable!(),
        }
    }
}

impl VerusCmd {
    const NOP: Self = Self {
        cargo_subcommand: CargoSubcommand::Nop,
        cargo_args: vec![],
        common_verus_driver_args: vec![],
        verify: false,
    };

    fn new(args: &[String]) -> Result<Self> {
        let mut cargo_args = vec![];
        let mut common_verus_driver_args: Vec<String> = vec![];

        let mut args_iter = args.iter();

        let command = args_iter.next().expect("main() ensures > 0 args");
        let (cargo_subcommand, just_verify) = match command.as_str() {
            "check" => (CargoSubcommand::Check, true),
            "verify" => (CargoSubcommand::Build, true),
            "build" => (CargoSubcommand::Build, false),
            "new" => {
                new_project(args)?;
                return Ok(Self::NOP);
            }
            cmd => bail!("Expected command `new`, `check`, `verify`, or `build`, found `{cmd}`"),
        };

        while let Some(arg) = args_iter.next() {
            match arg.as_str() {
                "--" => break,
                _ => {}
            }
            cargo_args.push(arg.clone());
        }

        common_verus_driver_args.extend_from_slice(&[
            "--VIA-CARGO".to_owned(),
            "compile-when-not-primary-package".to_owned(),
        ]);

        if !just_verify {
            common_verus_driver_args.extend_from_slice(&[
                "--VIA-CARGO".to_owned(),
                "compile-when-primary-package".to_owned(),
            ]);
        }

        common_verus_driver_args.extend(args_iter.cloned());

        Ok(Self { cargo_subcommand, cargo_args, common_verus_driver_args, verify: just_verify })
    }

    fn metadata(&self) -> Result<Metadata> {
        let standalone_flags = &["--frozen", "--locked", "--offline"];

        let flags_with_values = &["--config", "--manifest-path", "-Z"];

        let cargo_metadata_args =
            filter_args(self.cargo_args.iter(), standalone_flags, flags_with_values)?;

        let mut cmd = MetadataCommand::new();
        cmd.other_options(cargo_metadata_args);
        let metadata = cmd.exec()?;
        Ok(metadata)
    }

    fn into_std_cmd(self) -> Result<Command> {
        // TODO: use the "+ ... toolchain" argument?
        let mut cmd = Command::new(env::var("CARGO").unwrap_or("cargo".into()));

        cmd.arg(self.cargo_subcommand.to_arg().to_owned()).args(&self.cargo_args);

        cmd.env("RUSTC_WRAPPER", verus_driver_path());

        cmd.env(VERUS_DRIVER_VIA_CARGO, "1");

        // See https://github.com/rust-lang/cargo/blob/94aa7fb1321545bbe922a87cb11f5f4559e3be63/src/cargo/core/compiler/fingerprint/mod.rs#L71
        cmd.env("__CARGO_DEFAULT_LIB_METADATA", "verus");

        let common_verus_driver_args =
            pack_verus_driver_args_for_env(self.common_verus_driver_args.iter());

        if !common_verus_driver_args.is_empty() {
            cmd.env(VERUS_DRIVER_ARGS, common_verus_driver_args);
        }

        let metadata = self.metadata()?;
        let metadata_index = MetadataIndex::new(&metadata)?;

        let mut verified_something = false;
        for entry in metadata_index.entries() {
            let package = entry.package();

            let package_id =
                mk_package_id(&package.name, package.version.to_string(), &package.manifest_path);

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

        if self.verify && !verified_something {
            eprint!("{}", "\
WARNING: You asked for verification, but cargo did not find any crates that opted into verification. 
         If this is unexpected, try adding this entry to your Cargo.toml file:
            [package.metadata.verus]
            verify = true
".red());
        }

        Ok(cmd)
    }
}

fn filter_args(
    mut orig_args: impl Iterator<Item = impl AsRef<str>>,
    standalone_flags: &[impl AsRef<str>],
    flags_with_values: &[impl AsRef<str>],
) -> Result<Vec<String>> {
    let mut acc = vec![];
    while let Some(arg) = orig_args.next() {
        if standalone_flags.iter().any(|flag| flag.as_ref() == arg.as_ref()) {
            acc.push(arg.as_ref().to_owned());
        } else if flags_with_values.iter().any(|flag| flag.as_ref() == arg.as_ref()) {
            acc.push(arg.as_ref().to_owned());
            acc.push(
                orig_args
                    .next()
                    .ok_or_else(|| anyhow!("Expected {} to be followed by a value", arg.as_ref()))?
                    .as_ref()
                    .to_owned(),
            );
        } else {
            for flag in flags_with_values {
                if let Some(_val) = arg
                    .as_ref()
                    .strip_prefix(flag.as_ref())
                    .and_then(|without_flag| without_flag.strip_prefix("="))
                {
                    acc.push(arg.as_ref().to_owned());
                }
                break;
            }
        }
    }
    Ok(acc)
}

#[derive(Debug, Default, Deserialize)]
struct VerusMetadata {
    #[serde(default)]
    verify: bool,
    #[serde(rename = "no-vstd", default)]
    no_vstd: bool,
    #[serde(rename = "is-vstd", default)]
    is_vstd: bool,
    #[serde(rename = "is-core", default)]
    is_core: bool,
    #[serde(rename = "is-builtin", default)]
    is_builtin: bool,
    #[serde(rename = "is-builtin-macros", default)]
    is_builtin_macros: bool,
}

impl VerusMetadata {
    fn parse_from_package(package: &cargo_metadata::Package) -> Result<VerusMetadata> {
        match package.metadata.as_object().and_then(|obj| obj.get("verus")) {
            Some(value) => {
                serde_json::from_value::<VerusMetadata>(value.clone()).with_context(|| {
                    format!("Failed to parse {}-{}.metadata.verus", package.name, package.version)
                })
            }
            None => Ok(Default::default()),
        }
    }
}

struct MetadataIndex<'a> {
    entries: BTreeMap<&'a PackageId, MetadataIndexEntry<'a>>,
}

struct MetadataIndexEntry<'a> {
    package: &'a Package,
    verus_metadata: VerusMetadata,
    deps: BTreeMap<&'a str, &'a cargo_metadata::NodeDep>,
}

impl<'a> MetadataIndex<'a> {
    fn new(metadata: &'a Metadata) -> Result<Self> {
        assert!(metadata.resolve.is_some());
        let mut deps_by_package = BTreeMap::new();
        for node in &metadata.resolve.as_ref().unwrap().nodes {
            let mut deps = BTreeMap::new();
            for dep in &node.deps {
                assert!(deps.insert(dep.name.as_str(), dep).is_none());
            }
            assert!(deps_by_package.insert(&node.id, deps).is_none());
        }
        let mut entries = BTreeMap::new();
        for package in &metadata.packages {
            assert!(
                entries
                    .insert(
                        &package.id,
                        MetadataIndexEntry {
                            package,
                            verus_metadata: VerusMetadata::parse_from_package(package)?,
                            deps: deps_by_package.remove(&package.id).unwrap(),
                        }
                    )
                    .is_none()
            );
        }
        assert!(deps_by_package.is_empty());
        Ok(Self { entries })
    }

    fn get(&self, id: &PackageId) -> &MetadataIndexEntry<'a> {
        self.entries.get(id).unwrap()
    }

    fn entries(&self) -> impl Iterator<Item = &MetadataIndexEntry<'a>> {
        self.entries.values()
    }
}

impl<'a> MetadataIndexEntry<'a> {
    fn package(&self) -> &'a Package {
        self.package
    }

    fn verus_metadata(&self) -> &VerusMetadata {
        &self.verus_metadata
    }

    fn deps(&self) -> impl Iterator<Item = &&'a cargo_metadata::NodeDep> {
        self.deps.values()
    }
}

fn mk_package_id(
    name: impl AsRef<str>,
    version: impl AsRef<str>,
    manifest_path: impl AsRef<str>,
) -> String {
    // TODO: share code with rust_verify's version of this code
    let manifest_path_hash = {
        let mut hasher = Sha256::new();
        hasher.update(manifest_path.as_ref().as_bytes());
        hex::encode(hasher.finalize())
    };
    format!("{}-{}-{}", name.as_ref(), version.as_ref(), &manifest_path_hash[..12])
}

fn pack_verus_driver_args_for_env(args: impl Iterator<Item = impl AsRef<str>>) -> String {
    args.map(|arg| [VERUS_DRIVER_ARGS_SEP.to_owned(), arg.as_ref().to_owned()]).flatten().collect()
}

fn verus_driver_path() -> PathBuf {
    let mut path =
        env::current_exe().expect("current executable path invalid").with_file_name("verus");

    if cfg!(windows) {
        path.set_extension("exe");
    }

    path
}

#[must_use]
pub fn help_message() -> &'static str {
    "\
Usage:
    cargo verus <COMMAND> [OPTIONS] [--] [<ARGS>...]

OPTIONS are passed to 'cargo build' or 'cargo check', except the following, which are handled specially:
    -h, --help               Print this message
    -V, --version            Print version info and exit

Commands:
    new       Create a new Verus project
    verify    Verify the current crate with 'cargo build'
    build     Verify and build the current crate with 'cargo build'
    check     Runs the 'cargo check' subcommand

ARGS are passed to 'verus'.
"
}
