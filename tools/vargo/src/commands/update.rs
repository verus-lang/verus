use crate::cli::VargoOptions;
use crate::cli::VargoUpdate;
use crate::commands::cargo_run;
use crate::commands::AddOptions;
use crate::VargoContext;

impl AddOptions for VargoUpdate {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("update");
        cargo.args(&self.packages);
    }

    fn cmd_name(&self) -> &str {
        "update"
    }
}

pub fn update(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoUpdate,
) -> anyhow::Result<()> {
    if context.in_nextest {
        return Ok(());
    }

    cargo_run(options, context, vargo_cmd)
}
