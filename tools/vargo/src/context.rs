use std::path::Path;
use std::path::PathBuf;

use anyhow::Context;
use regex::Regex;

use crate::cli::VargoCli;
use crate::macros::info;
use crate::macros::warning;
use crate::smt_solver::SmtSolverBinary;
use crate::smt_solver::SmtSolverType;
use crate::util::VersionInfo;
use crate::VARGO_NEST;
use crate::VARGO_SOURCE_FILES;

fn get_vargo_nest() -> u64 {
    let vargo_nest = std::env::var("VARGO_NEST")
        .ok()
        .and_then(|x| x.parse().ok().map(|x: u64| x + 1))
        .unwrap_or(0);
    *VARGO_NEST.write().unwrap() = vargo_nest;
    std::env::set_var("VARGO_NEST", format!("{}", vargo_nest));
    vargo_nest
}

fn get_repo_root() -> anyhow::Result<PathBuf> {
    std::env::current_dir()
        .context("could not obtain the current directory")?
        .parent()
        .map(|p| p.to_owned())
        .ok_or_else(|| anyhow::anyhow!("current dir does not have a parent\nrun vargo in `source`"))
}

fn vargo_source_changed(repo_root: impl AsRef<Path>) -> anyhow::Result<bool> {
    let files = crate::util::vargo_file_contents(&repo_root.as_ref().join("tools").join("vargo"))?;
    // set at compile time
    let build_hash = &crate::util::hash_file_contents(VARGO_SOURCE_FILES.to_vec());
    let cur_hash =
        &crate::util::hash_file_contents(files.iter().map(|(f, n)| (f.as_str(), &n[..])).collect());
    Ok(build_hash != cur_hash)
}

fn get_rust_toolchain(
    repo_root: impl AsRef<Path>,
    in_nextest: bool,
) -> anyhow::Result<Option<String>> {
    fn run_rustup_toolchain() -> anyhow::Result<Vec<u8>> {
        let output = std::process::Command::new("rustup")
            .arg("show")
            .arg("active-toolchain")
            .stderr(std::process::Stdio::inherit())
            .output()
            .context("could not execute rustup")?;
        if !output.status.success() {
            anyhow::bail!("rustup failed");
        }
        Ok(output.stdout)
    }
    let rust_toolchain_toml = toml::from_str::<toml::Value>(
        &std::fs::read_to_string(repo_root.as_ref().join("rust-toolchain.toml"))
            .context("could not read rust-toolchain.toml\nrun vargo in `source`")?,
    )
    .context("could not parse Cargo.toml\nrun vargo in `source`")?;
    let rust_toolchain_channel_toml = rust_toolchain_toml
        .get("toolchain").and_then(|t| t.get("channel"))
                .and_then(|t| if let toml::Value::String(s) = t { Some(s) } else { None })
                .ok_or_else(||
                    anyhow::anyhow!("rust-toolchain.toml does not contain the toolchain.channel key, or it isn't a string\nrun vargo in `source`"))?;

    if !in_nextest {
        let active_toolchain_re =
            Regex::new(r"^(([A-Za-z0-9.-]+)-(?:aarch64|x86_64)-[A-Za-z0-9]+-[A-Za-z0-9-]+)")
                .unwrap();

        let rustup_output = run_rustup_toolchain()?;
        let stdout =
            std::str::from_utf8(&rustup_output).context("rustup output is invalid utf8")?;

        let mut captures = active_toolchain_re.captures_iter(stdout);
        if let Some(cap) = captures.next() {
            let channel = &cap[2];
            let toolchain = cap[1].to_string();
            if rust_toolchain_channel_toml != channel {
                anyhow::bail!(
                    "rustup is using a toolchain with channel {channel}, we expect {rust_toolchain_channel_toml}\ndo you have a rustup override set?");
            }
            Ok(Some(toolchain))
        } else {
            anyhow::bail!(
                "unexpected output from `rustup show active-toolchain`\nexpected a valid toolchain\ngot: {stdout}"
            )
        }
    } else {
        Ok(None)
    }
}

fn check_vargo_metadata_in_cargo_toml() -> anyhow::Result<()> {
    let cargo_toml = toml::from_str::<toml::Value>(
        &std::fs::read_to_string("Cargo.toml")
            .context("could not read Cargo.toml\nrun vargo in `source`")?,
    )
    .context("could not parse Cargo.toml\nrun vargo in `source`")?;
    let vargo_meta = cargo_toml
        .get("workspace")
        .and_then(|t| t.get("metadata"))
        .and_then(|t| t.get("vargo"))
        .ok_or_else(|| {
            anyhow::anyhow!(
            "Cargo.toml does not contain the workspace.metadata.vargo table\nrun vargo in `source`"
        )
        })?;

    if Some("workspace") != vargo_meta.get("tag").and_then(|t| t.as_str()) {
        anyhow::bail!("Cargo.toml does not have the vargo tag\nrun vargo in `source`");
    }

    Ok(())
}

/// Create the appropriate target directory (/targo-verus/debug or /target-verus/release)
fn create_target_verus_dir(release: bool) -> anyhow::Result<PathBuf> {
    let target_verus_dir =
        std::path::PathBuf::from("target-verus").join(if release { "release" } else { "debug" });
    if !target_verus_dir.exists() {
        info!("creating {}", target_verus_dir.display());
        std::fs::create_dir_all(&target_verus_dir)
            .context("could not create target-verus directory")?;
    }
    Ok(target_verus_dir)
}

#[derive(Debug)]
pub struct VargoContext {
    pub vargo_nest: u64,
    pub repo_root: PathBuf,
    pub rust_toolchain: Option<String>,
    pub in_nextest: bool,
    pub solver_binary_z3: SmtSolverBinary,
    pub solver_binary_cvc5: Option<SmtSolverBinary>,
    pub verus_version: Option<VersionInfo>,
    pub target_verus_artifact_dir_absolute: PathBuf,
    pub target_verus_dir: PathBuf,
    pub target_dir: PathBuf,
}

impl VargoContext {
    pub fn construct(cli: &VargoCli) -> anyhow::Result<Self> {
        check_vargo_metadata_in_cargo_toml()?;
        let vargo_nest = get_vargo_nest();
        let repo_root = get_repo_root()?;
        let in_nextest = std::env::var("VARGO_IN_NEXTEST").is_ok();
        let rust_toolchain = get_rust_toolchain(&repo_root, in_nextest)?;

        if vargo_nest == 0 && vargo_source_changed(&repo_root)? {
            anyhow::bail!(
                "vargo sources have changed since it was last built, please re-build vargo"
            );
        }

        let solver_binary_z3 = SmtSolverBinary::find_path(SmtSolverType::Z3, vargo_nest)
            .expect("find_path for Z3 always returns a path");
        let solver_binary_cvc5 = SmtSolverBinary::find_path(SmtSolverType::Cvc5, vargo_nest);

        // check binary versions
        if vargo_nest == 0
            && cli.command.needs_solver_version_check()
            && cli.options.solver_version_check
        {
            solver_binary_z3.check_version()?;
            if let Some(cvc5) = &solver_binary_cvc5 {
                cvc5.check_version()?;
            }
        }

        let verus_version = match crate::util::version_info(&repo_root) {
            Ok(version_info) => Some(version_info),
            Err(err) => {
                warning!(
                    "could not obtain version info from git, this will result in a binary with an unknown version: {err}"
                );
                None
            }
        };

        let target_verus_artifact_dir = create_target_verus_dir(cli.command.release())?;
        let target_verus_dir = target_verus_artifact_dir
            .parent()
            .expect("target artifact dir always has a parent")
            .to_path_buf();
        let target_dir = std::path::PathBuf::from("target");
        let target_verus_artifact_dir_absolute = std::fs::canonicalize(&target_verus_artifact_dir)
            .with_context(|| {
                format!(
                    "could not canonicalize target-verus directory: {}",
                    target_verus_artifact_dir.display()
                )
            })?;

        Ok(VargoContext {
            in_nextest,
            rust_toolchain,
            target_dir,
            target_verus_dir,
            target_verus_artifact_dir_absolute,
            vargo_nest,
            repo_root,
            solver_binary_z3,
            solver_binary_cvc5,
            verus_version,
        })
    }
}
