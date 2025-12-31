use anyhow::Context;
use regex::Regex;

use std::fmt::Display;
use std::path::Path;

use crate::consts;
use crate::macros::warning;

#[derive(Clone, Debug)]
pub enum SmtSolverType {
    Z3,
    Cvc5,
}

impl SmtSolverType {
    fn executable_name(&self) -> String {
        let base = match self {
            SmtSolverType::Z3 => "z3",
            SmtSolverType::Cvc5 => "cvc5",
        };
        if cfg!(target_os = "windows") {
            format!(".\\{}.exe", base)
        } else {
            format!("./{}", base)
        }
    }

    fn env_var_name(&self) -> &str {
        match self {
            SmtSolverType::Z3 => "VERUS_Z3_PATH",
            SmtSolverType::Cvc5 => "VERUS_CVC5_PATH",
        }
    }

    fn version_re(&self) -> Regex {
        match self {
            SmtSolverType::Z3 => Regex::new(r"Z3 version (\d+\.\d+\.\d+) - \d+ bit")
                .expect("failed to compile Z3 version regex"),
            SmtSolverType::Cvc5 => Regex::new(r"This is cvc5 version (\d+\.\d+\.\d+)")
                .expect("failed to compile cvc5 version regex"),
        }
    }

    fn expected_version(&self) -> String {
        match self {
            SmtSolverType::Z3 => consts::EXPECTED_Z3_VERSION.to_string(),
            SmtSolverType::Cvc5 => consts::EXPECTED_CVC5_VERSION.to_string(),
        }
    }
}

impl Display for SmtSolverType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtSolverType::Cvc5 => f.write_str("cvc5"),
            SmtSolverType::Z3 => f.write_str("z3"),
        }
    }
}

#[derive(Debug)]
pub struct SmtSolverBinary {
    pub stype: SmtSolverType,
    pub path: std::path::PathBuf,
}

impl SmtSolverBinary {
    pub fn find_path(solver_type: SmtSolverType, vargo_nest: u64) -> Option<Self> {
        let find_path_inner = || {
            let file_name = if std::env::var(solver_type.env_var_name()).is_ok() {
                std::env::var(solver_type.env_var_name()).unwrap()
            } else {
                solver_type.executable_name()
            };
            let path = std::path::Path::new(&file_name);

            if !path.is_file() && vargo_nest == 0 {
                // When we fail to find Z3, we warning the user but optimistically continue
                // Since we don't currently use cvc5, we don't warning the user about it, and we bail out
                match solver_type {
                    SmtSolverType::Z3 => warning!(
                        "{file_name} not found -- this is likely to cause errors or a broken build\nrun `tools/get-z3.(sh|ps1)` first"
                    ),
                    SmtSolverType::Cvc5 => return None,
                }
            }
            if std::env::var(solver_type.env_var_name()).is_err() && path.is_file() {
                std::env::set_var(solver_type.env_var_name(), path);
            }
            Some(path.to_path_buf())
        };
        let path = find_path_inner();
        if matches!(solver_type, SmtSolverType::Z3) {
            assert!(path.is_some());
        }
        path.map(|path| SmtSolverBinary {
            stype: solver_type,
            path,
        })
    }

    pub fn check_version(&self) -> anyhow::Result<()> {
        let output = std::process::Command::new(&self.path)
            .arg("--version")
            .output()
            .with_context(|| format!("could not execute {}", self.stype))?;
        if !output.status.success() {
            anyhow::bail!("{} returned non-zero exit code", self.stype);
        }
        let stdout_str = std::str::from_utf8(&output.stdout)
            .with_context(|| format!("{} version output is not valid utf8", self.stype))?
            .to_string();

        let version = self
            .stype
            .version_re()
            .captures(&stdout_str)
            .and_then(|captures| {
                let mut captures = captures.iter();
                let _ = captures.next()?;
                let version = captures.next()?;
                if captures.next().is_some() {
                    None
                } else {
                    Some(version?.as_str())
                }
            })
            .ok_or_else(|| {
                anyhow::anyhow!("unexpected {} version output ({})", self.stype, stdout_str)
            })?;
        if version != self.stype.expected_version() {
            anyhow::bail!(
                 "Verus expects {name} version \"{expected}\", found version \"{version}\"\n\
            Run ./tools/get-{name}.(sh|ps1) to update {name} first.\n\
            If you need a build with a custom {name} version, re-run with --no-solver-version-check.",
                name=self.stype,
                expected=self.stype.expected_version(),
            );
        } else {
            Ok(())
        }
    }

    pub fn copy_to_target_dir(
        &self,
        target_verus_dir: impl AsRef<Path>,
        macos_prepare_script: &mut String,
    ) -> anyhow::Result<()> {
        let target_verus_dir = target_verus_dir.as_ref();
        if self.path.is_file() {
            let from_f = &self.path;
            let to_f = target_verus_dir.join(self.stype.executable_name());
            if to_f.exists() {
                // If we directly overwrite a binary it can cause
                // a code-signing issue on macs. To work around this, we
                // delete the old file first before moving the new one.
                std::fs::remove_file(&to_f).unwrap();
            }
            std::fs::copy(from_f, &to_f).with_context(|| {
                format!(
                    "could not copy file {} to {}",
                    from_f.display(),
                    to_f.display()
                )
            })?;

            let dest_file_name = to_f
                .file_name()
                .ok_or_else(|| anyhow::anyhow!("could not get file name for {}", self.stype))?;
            macos_prepare_script.push_str(
                format!(
                    "\nxattr -d com.apple.quarantine {}\n",
                    dest_file_name.to_string_lossy()
                )
                .as_str(),
            );
        }
        Ok(())
    }
}
