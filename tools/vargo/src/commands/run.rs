use crate::cli::VargoBuild;
use crate::cli::VargoOptions;
use crate::cli::VargoRun;
use crate::commands::build;
use crate::commands::cargo_run;
use crate::commands::AddOptions;
use crate::macros::info;
use crate::VargoContext;

impl AddOptions for VargoRun {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("run");

        if self.build_options.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }

        self.feature_options.add_options(cargo);

        if !self.verus_args.is_empty() {
            cargo.arg("--");
            cargo.args(&self.verus_args);
        }
    }

    fn cmd_name(&self) -> &str {
        "run"
    }
}

impl VargoRun {
    fn build_cmd(&self) -> VargoBuild {
        VargoBuild {
            package: None,
            exclude: Default::default(),
            feature_options: self.feature_options.clone(),
            build_options: self.build_options.clone(),
            verus_args: self.verus_args.clone(),
        }
    }
}

pub fn run(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoRun,
) -> anyhow::Result<()> {
    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.as_deref() != Some("air")
        && vargo_cmd.package.as_deref() != Some("rust_verify")
    {
        if let Some(p) = vargo_cmd.package.as_deref() {
            anyhow::bail!("unexpected package for `vargo run`: {p}")
        } else {
            anyhow::bail!("unexpected package for `vargo run`")
        }
    }

    // may need to rebuild rust_verify
    if vargo_cmd.package.as_deref() == Some("rust_verify") {
        build(options, context, &vargo_cmd.build_cmd())?;
        info!(
            "rebuilding: done{}",
            if vargo_cmd.build_options.release {
                " (release)"
            } else {
                ""
            }
        );
    }

    cargo_run(options, context, vargo_cmd)
}
