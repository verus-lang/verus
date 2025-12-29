use crate::cli::VargoBuild;
use crate::cli::VargoOptions;
use crate::cli::VargoRun;
use crate::commands::build;
use crate::commands::cargo_command;
use crate::commands::log_command;
use crate::macros::info;
use crate::VargoContext;
use crate::VargoResult;

impl VargoRun {
    pub fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("run");

        if self.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        }

        if self.no_default_features {
            cargo.arg("--no-default-features");
        }

        for feature in &self.features {
            cargo.arg("--features");
            cargo.arg(format!("{feature}"));
        }

        if !self.verus_args.is_empty() {
            cargo.arg("--");
            cargo.args(&self.verus_args);
        }
    }

    fn build_cmd(&self) -> VargoBuild {
        VargoBuild {
            package: None,
            exclude: Default::default(),
            no_default_features: self.no_default_features,
            features: self.features.clone(),
            release: self.release,
            build_options: self.build_options.clone(),
            verus_args: self.verus_args.clone(),
        }
    }
}

pub fn run(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoRun,
) -> VargoResult<()> {
    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.as_deref() != Some("air")
        && vargo_cmd.package.as_deref() != Some("rust_verify")
    {
        return Err(format!(
            "unexpected package for `vargo run`{}",
            if let Some(p) = vargo_cmd.package.as_deref() {
                format!(": {p}")
            } else {
                "".to_owned()
            }
        ));
    }

    // may need to rebuild rust_verify
    if vargo_cmd.package.as_deref() == Some("rust_verify") {
        build(options, context, &vargo_cmd.build_cmd())?;
        info!(
            "rebuilding: done{}",
            if vargo_cmd.release { " (release)" } else { "" }
        );
    }

    if context.in_nextest {
        return Ok(());
    }

    let mut cargo = cargo_command(options, context);
    vargo_cmd.add_options(&mut cargo);
    log_command(&cargo, options.vargo_verbose);
    let status = cargo
        .status()
        .map_err(|x| format!("could not execute cargo ({})", x))?;

    Ok(())
}
