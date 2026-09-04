use std::collections::BTreeMap as Map;
use std::env::consts::{DLL_EXTENSION, DLL_PREFIX};
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, bail};
use cargo_metadata::PackageId;
use cargo_metadata::camino::{Utf8Path, Utf8PathBuf};

#[derive(Clone, Debug)]
pub struct VstdBuild {
    pub vstd_id: PackageId,
    pub deps: Map<String, PackageId>,
}

/// Special code path for when `vstd` is the only primary package to build.
///
/// Artifacts related to `vstd` must be hoisted to the output directory, so that e.g.
/// `rust_analyzer` can receive them as `--extern` inputs, unaware of Cargo's layout.
///
/// The list of files to hoist is hardwired:
/// - `libvstd.rlib` (automatically handled by Cargo)
/// - `vstd.vir`
/// - `libverus_builtin.rlib`
/// - `libverus_builtin_macros.dylib`
/// - `libverus_state_machines_macros.dylib`
///
/// The implementation makes the following assumptions:
/// - Files to hoist are siblings of `vstd.rmeta`.
/// - The output dir is the parent of `vstd.rlib`.
///
pub fn build_vstd(vstd_build: &VstdBuild, mut command: Command) -> Result<ExitCode> {
    // Collect artifact files related to `vstd` or its deps.
    let mut artifacts = Map::<&str, cargo_metadata::Artifact>::new();
    command
        .arg("--message-format=json-render-diagnostics")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::inherit());
    let mut child = command.spawn().context("failed to spawn cargo")?;
    let stdout = child.stdout.take().expect("stdout was piped");
    for message in cargo_metadata::Message::parse_stream(std::io::BufReader::new(stdout)) {
        match message? {
            cargo_metadata::Message::CompilerArtifact(artifact) => {
                if artifact.package_id == vstd_build.vstd_id {
                    artifacts.insert("vstd", artifact);
                } else if let Some((name, _)) = vstd_build
                    .deps
                    .iter()
                    .find(|(_, package_id)| artifact.package_id == **package_id)
                {
                    artifacts.insert(name, artifact);
                }
            }
            cargo_metadata::Message::CompilerMessage(message) => {
                if let Some(rendered) = message.message.rendered {
                    eprint!("{rendered}");
                }
            }
            cargo_metadata::Message::TextLine(line) => eprintln!("{line}"),
            _ => {}
        }
    }

    let exit_status = child.wait().context("failed to wait for cargo")?;
    let Some(code) = exit_status.code() else {
        bail!("Command {command:?} did not succeed: {exit_status}");
    };
    let exit_code = u8::try_from(code)
        .map(From::from)
        .with_context(|| format!("Command {command:?} returned an odd exit code: {code}"))?;
    if exit_code != ExitCode::SUCCESS {
        return Ok(exit_code);
    }

    let get_artifact_file = |name: &str, ext: &str| -> Result<&Utf8PathBuf> {
        artifacts
            .get(name)
            .with_context(|| format!("no artifact named `{name}`"))?
            .filenames
            .iter()
            .find(|path| path.extension() == Some(ext))
            .with_context(|| format!("no artifact file with extension `.{ext}`"))
    };

    // Compute relevant paths.
    let vstd_rlib = get_artifact_file("vstd", "rlib")?;
    let vstd_rmeta = get_artifact_file("vstd", "rmeta")?;
    let verus_builtin_rlib = get_artifact_file("verus_builtin", "rlib")?;
    let verus_builtin_macros_dylib = get_artifact_file("verus_builtin_macros", DLL_EXTENSION)?;
    let verus_state_machines_macros_dylib =
        get_artifact_file("verus_state_machines_macros", DLL_EXTENSION)?;

    fn copy_file(src: &Utf8Path, dst: &Utf8Path) -> Result<()> {
        let _ = std::fs::copy(src.as_std_path(), dst.as_std_path())
            .with_context(|| format!("copying {src} to {dst}"))?;
        Ok(())
    }

    // Hoist files.
    copy_file(&vstd_rmeta.with_extension("vir"), &vstd_rlib.with_file_name("vstd.vir"))?;
    copy_file(verus_builtin_rlib, &vstd_rlib.with_file_name("libverus_builtin.rlib"))?;
    copy_file(
        verus_builtin_macros_dylib,
        &vstd_rlib.with_file_name(format!("{DLL_PREFIX}verus_builtin_macros.{DLL_EXTENSION}")),
    )?;
    copy_file(
        verus_state_machines_macros_dylib,
        &vstd_rlib
            .with_file_name(format!("{DLL_PREFIX}verus_state_machines_macros.{DLL_EXTENSION}")),
    )?;

    Ok(exit_code)
}
