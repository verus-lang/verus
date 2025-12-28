use crate::cli::VargoMetadata;
use crate::cli::VargoOptions;
use crate::commands::log_command;
use crate::VargoContext;
use crate::VargoResult;

use crate::commands::cargo_command;

impl VargoMetadata {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("metadata");
        cargo.args(["--format-version", self.format_version.as_str()]);

        self.feature_options.add_options(cargo);
    }
}

pub fn metadata(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoMetadata,
) -> VargoResult<()> {
    let mut cargo = cargo_command(options, context);
    vargo_cmd.add_options(&mut cargo);
    log_command(&cargo, options.vargo_verbose);

    let status = cargo
        .status()
        .map_err(|x| format!("could not execute cargo ({})", x))?;

    if !status.success() {
        return Err(format!(
            "`cargo metadata` returned status code {:?}",
            status.code()
        ));
    }

    Ok(())
}
