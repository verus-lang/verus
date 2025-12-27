use std::path::Path;

use crate::cli::VargoClean;
use crate::cli::VargoOptions;
use crate::commands::cargo_command;
use crate::commands::clean_vstd;
use crate::commands::log_command;
use crate::info;
use crate::VargoContext;
use crate::VargoResult;

impl VargoClean {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("clean");

        if self.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }
    }
}

pub fn clean(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoClean,
) -> VargoResult<()> {
    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.as_deref() == Some("vstd") {
        clean_vstd(&context.target_verus_dir)?;
    } else {
        let mut cargo = cargo_command(options, context);
        vargo_cmd.add_options(&mut cargo);
        log_command(&cargo, options.vargo_verbose);
        let status = cargo
            .status()
            .map_err(|x| format!("could not execute cargo ({})", x))?;

        if !status.success() {
            return Err(format!(
                "`cargo clean` returned status code {:?}",
                status.code()
            ));
        }

        let release_target_verus = context.target_verus_dir.join("release");
        remove_target_verus_dir(&context.target_verus_artifact_dir_absolute)?;
        remove_target_verus_dir(&release_target_verus)?;
    }

    Ok(())
}

fn remove_target_verus_dir(path: impl AsRef<Path>) -> VargoResult<()> {
    let path = path.as_ref();
    if path.is_dir() && path.exists() {
        info!("removing {}", path.display());
        std::fs::remove_dir_all(path)
            .map_err(|e| format!("could not remove target-verus directory ({e})"))?
    }

    Ok(())
}
