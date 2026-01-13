use crate::cli::VargoMetadata;
use crate::cli::VargoOptions;
use crate::commands::cargo_run;
use crate::commands::AddOptions;
use crate::VargoContext;

impl AddOptions for VargoMetadata {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("metadata");
        cargo.args(["--format-version", self.format_version.as_str()]);

        self.feature_options.add_options(cargo);
    }

    fn cmd_name(&self) -> &str {
        "metadata"
    }
}

pub fn metadata(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoMetadata,
) -> anyhow::Result<()> {
    cargo_run(options, context, vargo_cmd)
}
