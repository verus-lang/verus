use crate::cli::VargoOptions;
use crate::cli::VargoUpdate;
use crate::commands::cargo_command;
use crate::commands::log_command;
use crate::VargoContext;
use crate::VargoResult;

impl VargoUpdate {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("update");
        cargo.args(&self.packages);
    }
}

pub fn update(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoUpdate,
) -> VargoResult<()> {
    if context.in_nextest {
        return Ok(());
    }

    let mut cargo = cargo_command(options, context);
    vargo_cmd.add_options(&mut cargo);
    log_command(&cargo, options.vargo_verbose);

    let status = cargo
        .status()
        .map_err(|x| format!("could not execute cargo ({})", x))?;

    if !status.success() {
        return Err(format!(
            "`cargo update` returned status code {:?}",
            status.code()
        ));
    }

    Ok(())
}
