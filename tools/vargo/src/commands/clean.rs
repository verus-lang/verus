use std::path::Path;

use anyhow::Context;

use crate::cli::VargoClean;
use crate::cli::VargoOptions;
use crate::commands::cargo_run;
use crate::commands::clean_vstd;
use crate::commands::AddOptions;
use crate::info;
use crate::VargoContext;

impl AddOptions for VargoClean {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("clean");

        if self.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }
    }

    fn cmd_name(&self) -> &str {
        "clean"
    }
}

pub fn clean(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoClean,
) -> anyhow::Result<()> {
    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.as_deref() == Some("vstd") {
        clean_vstd(&context.target_verus_dir)?;
    } else {
        cargo_run(options, context, vargo_cmd)?;

        let release_target_verus = context.target_verus_dir.join("release");
        remove_target_verus_dir(&context.target_verus_artifact_dir_absolute)?;
        remove_target_verus_dir(&release_target_verus)?;
    }

    Ok(())
}

fn remove_target_verus_dir(path: impl AsRef<Path>) -> anyhow::Result<()> {
    let path = path.as_ref();
    if path.is_dir() && path.exists() {
        info!("removing {}", path.display());
        std::fs::remove_dir_all(path).with_context(|| {
            format!("could not remove target-verus directory {}", path.display())
        })?
    }

    Ok(())
}
