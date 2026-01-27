use std::path::Path;

use anyhow::Context;
use filetime::FileTime as FFileTime;

use crate::cli::VargoBuild;
use crate::cli::VargoOptions;
use crate::cli::VerusFeatures;
use crate::commands::cargo_command;
use crate::commands::cargo_run;
use crate::commands::clean_vstd;
use crate::commands::log_command;
use crate::commands::AddOptions;
use crate::context::VargoContext;
use crate::lib_exe_names::EXE;
use crate::lib_exe_names::LIB_DL;
use crate::lib_exe_names::LIB_PRE;
use crate::macros::info;
use crate::util;
use crate::VERUS_ROOT_FILE;
use crate::VSTD_FILES;

use serde::Deserialize;
use serde::Serialize;

use std::fmt::Write;

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash, Debug, Deserialize, Serialize)]
struct FileTime {
    seconds: i64,
    nanos: u32,
}

impl From<FFileTime> for FileTime {
    fn from(value: FFileTime) -> Self {
        FileTime {
            seconds: value.seconds(),
            nanos: value.nanoseconds(),
        }
    }
}

#[derive(Debug, Deserialize, Serialize, Eq, PartialEq)]
struct Fingerprint {
    dependencies_mtime: FileTime,
    vstd_mtime: FileTime,
    vstd_no_std: bool,
    vstd_no_alloc: bool,
}

impl PartialOrd for Fingerprint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.vstd_no_std != other.vstd_no_std || self.vstd_no_alloc != other.vstd_no_alloc {
            None
        } else {
            use std::cmp::Ordering::*;
            match (
                self.dependencies_mtime.cmp(&other.dependencies_mtime),
                self.vstd_mtime.cmp(&other.vstd_mtime),
            ) {
                (Less, Less) => Some(Less),
                (Equal, Equal) => Some(Equal),
                (Greater, Greater) => Some(Greater),
                _ => None,
            }
        }
    }
}

impl AddOptions for VargoBuild {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("build");

        if self.build_options.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }

        for exclude in &self.exclude {
            let e = exclude.as_str();
            cargo.args(["--exclude", e]);
        }

        self.feature_options.add_options(cargo);
    }

    fn cmd_name(&self) -> &str {
        "build"
    }
}

impl VargoBuild {
    fn cmd_for_package(&self, package: &str) -> Self {
        let mut cpy = self.clone();
        cpy.package = Some(package.to_owned());
        cpy.apply_feature_filter();
        cpy
    }

    /// Filter features based on the supported features for the packages
    fn apply_feature_filter(&mut self) {
        match self.package.as_deref() {
            Some("rust_verify") => {
                self.feature_options
                    .filter_feature_list(&[VerusFeatures::Singular]);
            }
            Some("verus") => {
                self.feature_options
                    .filter_feature_list(&[VerusFeatures::RecordHistory]);
            }
            _ => {
                self.feature_options.features = Vec::new();
            }
        }
    }
}

pub fn build(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoBuild,
) -> anyhow::Result<()> {
    const PACKAGES: &[&str; 7] = &[
        "rust_verify",
        "verus_builtin",
        "verus_builtin_macros",
        "verus_state_machines_macros",
        "vstd_build",
        "verus",
        "cargo-verus",
    ];

    if context.in_nextest {
        return Ok(());
    }

    if matches!(vargo_cmd.package.as_deref(), Some("air" | "verusdoc")) {
        return build_target(options, context, vargo_cmd);
    }

    let should_build_vstd = if let Some(package) = vargo_cmd.package.as_deref() {
        if PACKAGES.contains(&package) {
            false
        } else if package == "vstd" {
            true
        } else {
            anyhow::bail!("unknown package {package}");
        }
    } else {
        true
    };
    let vstd_is_excluded = vargo_cmd.exclude.iter().any(|e| e.as_str() == "vstd");
    let build_vstd = should_build_vstd && !vstd_is_excluded;

    if vargo_cmd.package.is_some() {
        let mut vargo_cmd = vargo_cmd.clone();
        vargo_cmd.apply_feature_filter();
        build_target(options, context, &vargo_cmd)?;
    } else {
        for package in PACKAGES.iter().filter(|p| !vargo_cmd.exclude.contains(**p)) {
            let vargo_cmd = vargo_cmd.cmd_for_package(package);
            build_target(options, context, &vargo_cmd)?;
        }
    }

    let mut dependencies_mtime = None;
    let mut dependency_missing = false;

    let mut macos_prepare_script = r#"#!/bin/bash
set -e
set -x

cd "$( dirname "${{BASH_SOURCE[0]}}" )"

"#
    .to_owned();

    for from_f_name in [
        "libverus_builtin.rlib".to_owned(),
        format!("{}verus_builtin_macros.{}", LIB_PRE, LIB_DL),
        format!("{}verus_state_machines_macros.{}", LIB_PRE, LIB_DL),
        format!("rust_verify{}", EXE),
        format!("verus{}", EXE),
        format!("cargo-verus{}", EXE),
    ]
    .into_iter()
    {
        let from_f = context
            .target_dir
            .join(if vargo_cmd.build_options.release {
                "release"
            } else {
                "debug"
            })
            .join(&from_f_name);
        if from_f.exists() {
            let from_f_meta = from_f
                .metadata()
                .with_context(|| format!("cannot obtain metadata for {from_f_name}"))?;
            dependencies_mtime = Some(
                dependencies_mtime
                    .unwrap_or(FFileTime::zero())
                    .max(FFileTime::from_last_modification_time(&from_f_meta)),
            );
            let to_f = context
                .target_verus_artifact_dir_absolute
                .join(&from_f_name);
            // info!(
            //     "copying {} to {}",
            //     from_f.display(),
            //     to_f.display()
            // );

            if to_f.exists() {
                // If we directly overwrite a binary it can cause
                // a code-signing issue on macs. To work around this, we
                // delete the old file first before moving the new one.
                std::fs::remove_file(&to_f).unwrap();
            }

            std::fs::copy(&from_f, &to_f).with_context(|| {
                format!(
                    "could not copy file {} to {}",
                    from_f.display(),
                    to_f.display()
                )
            })?;

            writeln!(
                &mut macos_prepare_script,
                "xattr -d com.apple.quarantine {}",
                from_f_name
            )
            .context("could not write to macos prepare script")?;
        } else {
            dependency_missing = true;
        }
    }

    context.solver_binary_z3.copy_to_target_dir(
        &context.target_verus_artifact_dir_absolute,
        &mut macos_prepare_script,
    )?;
    if let Some(cvc5) = &context.solver_binary_cvc5 {
        cvc5.copy_to_target_dir(
            &context.target_verus_artifact_dir_absolute,
            &mut macos_prepare_script,
        )?;
    }

    let fingerprint_path = context
        .target_verus_artifact_dir_absolute
        .join(".vstd-fingerprint");

    for file in ["vstd.vir", "libvstd.rlib"] {
        if !context
            .target_verus_artifact_dir_absolute
            .join(file)
            .exists()
            && fingerprint_path.exists()
        {
            info!("removing {}", fingerprint_path.display());
            std::fs::remove_file(&fingerprint_path)
                .with_context(|| format!("could not delete file {}", fingerprint_path.display()))?;
        }
    }

    for src in ["builtin", "builtin_macros", "state_machines_macros", "vstd"] {
        let from_d = std::path::Path::new(src);
        let to_d = context.target_verus_artifact_dir_absolute.join(src);

        if to_d.exists() {
            std::fs::remove_dir_all(&to_d).unwrap();
        }
        copy_dir(from_d, &to_d, &[std::path::Path::new("target")]).with_context(|| {
            format!(
                "could not copy source directory {} to {}",
                from_d.display(),
                to_d.display()
            )
        })?;
    }

    let stored_fingerprint = if fingerprint_path.exists() {
        let s = std::fs::read_to_string(&fingerprint_path)
            .with_context(|| format!("cannot read {}", fingerprint_path.display()))?;
        let f = toml::from_str::<Fingerprint>(&s).with_context(|| {
            format!(
                "cannot parse {}, try `vargo clean -p vstd` (first), or `vargo clean`",
                fingerprint_path.display()
            )
        })?;
        Some(f)
    } else {
        None
    };

    if build_vstd {
        if dependency_missing {
            info!("not all of the vstd dependencies are built, skipping vstd build");

            clean_vstd(&context.target_verus_artifact_dir_absolute)?;
        } else {
            let dependencies_mtime: FileTime = dependencies_mtime
                .expect("dependencies_mtime should be Some here")
                .into();

            let vstd_path = std::path::Path::new("vstd");
            let vstd_mtime: FileTime = util::mtime_recursive(vstd_path)?.into();

            let current_fingerprint = Fingerprint {
                dependencies_mtime,
                vstd_mtime,
                vstd_no_std: vargo_cmd.build_options.vstd_no_std,
                vstd_no_alloc: vargo_cmd.build_options.vstd_no_alloc,
            };

            if stored_fingerprint
                .as_ref()
                .map(|s| {
                    matches!(
                        current_fingerprint.partial_cmp(s),
                        Some(std::cmp::Ordering::Greater) | None
                    )
                })
                .unwrap_or(true)
            {
                info!("vstd outdated, rebuilding");
                rebuild_vstd(
                    options,
                    context,
                    vargo_cmd,
                    &fingerprint_path,
                    &current_fingerprint,
                )?
            } else {
                info!("vstd fresh");
            }
        }
    }

    #[cfg(target_os = "macos")]
    {
        let macos_prepare_script_path = context
            .target_verus_artifact_dir_absolute
            .join("macos_allow_gatekeeper.sh");
        std::fs::write(&macos_prepare_script_path, macos_prepare_script)
            .map_err(|x| anyhow::anyhow!("could not write to macos prepare script ({})", x))?;
        std::fs::set_permissions(
            &macos_prepare_script_path,
            <std::fs::Permissions as std::os::unix::fs::PermissionsExt>::from_mode(0o755),
        )
        .map_err(|x| {
            anyhow::anyhow!("could not set permissions on macos prepare script ({})", x)
        })?;
    }

    if let Some(version_info) = &context.verus_version {
        let version_info_path = context
            .target_verus_artifact_dir_absolute
            .join("version.txt");
        std::fs::write(&version_info_path, version_info.version.as_str()).with_context(|| {
            format!(
                "could not write to version file {}",
                version_info_path.display()
            )
        })?;
    }

    let verus_root_path = context
        .target_verus_artifact_dir_absolute
        .join(VERUS_ROOT_FILE);
    if dependency_missing
        || VSTD_FILES.iter().any(|f| {
            let f = context.target_verus_artifact_dir_absolute.join(f);
            !f.is_file()
        })
    {
        if verus_root_path.exists() {
            info!("removing {}", verus_root_path.display());
            std::fs::remove_file(&verus_root_path)
                .with_context(|| format!("could not delete file {}", verus_root_path.display()))?;
        }
    } else {
        std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(&verus_root_path)
            .with_context(|| format!("could not touch file {}", verus_root_path.display()))?;
    }
    Ok(())
}

fn build_target(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoBuild,
) -> anyhow::Result<()> {
    assert!(vargo_cmd.package.is_some());
    info!(
        "building {}",
        vargo_cmd
            .package
            .as_deref()
            .expect("when building a particular target, package is set")
    );

    cargo_run(options, context, vargo_cmd)
}

fn copy_dir(
    src: &std::path::Path,
    dest: &std::path::Path,
    exclude: &[&std::path::Path],
) -> std::io::Result<()> {
    assert!(exclude.iter().all(|x| x.is_relative()));
    copy_dir_internal(src, dest, exclude, 0)
}

fn copy_dir_internal(
    src: &std::path::Path,
    dest: &std::path::Path,
    exclude: &[&std::path::Path],
    depth: usize,
) -> std::io::Result<()> {
    std::fs::create_dir_all(dest)?;
    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let path = entry.path();
        let dest_path = dest.join(path.file_name().unwrap());
        if exclude.iter().any(|xcl| {
            let xcl = xcl.iter().skip(depth).collect::<std::path::PathBuf>();
            path.starts_with(xcl)
        }) {
            continue;
        }
        if entry.file_type()?.is_dir() {
            copy_dir(&path, &dest_path, exclude)?;
        } else {
            std::fs::copy(&path, &dest_path)?;
        }
    }
    Ok(())
}

fn rebuild_vstd(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoBuild,
    fingerprint_path: &Path,
    current_fingerprint: &Fingerprint,
) -> anyhow::Result<()> {
    let mut vstd_build = cargo_command(options, context);
    vstd_build.args(["run", "--package", "vstd_build"]);
    if vargo_cmd.build_options.release {
        vstd_build.arg("--release");
    }

    vstd_build
        .arg("--")
        .arg(&context.target_verus_artifact_dir_absolute);
    // TODO(bsdinis): when vstd_build supports it, forward verus_args here

    // release is doubled because one is for cargo and the other for vstd_build
    if vargo_cmd.build_options.release {
        vstd_build.arg("--release");
    }
    if vargo_cmd.build_options.vstd_no_verify {
        vstd_build.arg("--no-verify");
    }
    if vargo_cmd.build_options.vstd_no_std {
        vstd_build.arg("--no-std");
    }
    if vargo_cmd.build_options.vstd_no_alloc {
        vstd_build.arg("--no-alloc");
    }
    if vargo_cmd.build_options.vstd_trace {
        vstd_build.arg("--trace");
    }
    if vargo_cmd.build_options.vstd_log_all {
        vstd_build.arg("--log-all");
    }
    if options.vargo_verbose {
        vstd_build.arg("--verbose");
    }
    if !options.solver_version_check {
        vstd_build.arg("--no-solver-version-check");
    }
    log_command(&vstd_build, options.vargo_verbose);

    vstd_build
        .status()
        .context("could not execute cargo")
        .and_then(|x| {
            if x.success() {
                Ok(())
            } else if let Some(code) = x.code() {
                Err(anyhow::anyhow!("vstd_build returned status code {code}"))
            } else {
                Err(anyhow::anyhow!("vstd_build was terminated by a signal"))
            }
        })?;

    std::fs::write(
        fingerprint_path,
        toml::to_string(&current_fingerprint).expect("failed to serialize fingerprint"),
    )
    .with_context(|| {
        format!(
            "cannot write fingerprint file {}",
            fingerprint_path.display()
        )
    })
}
