use crate::cli::VargoBuild;
use crate::cli::VargoNextestRun;
use crate::cli::VargoOptions;
use crate::cli::VerusFeatures;
use crate::commands::build;
use crate::commands::cargo_command;
use crate::commands::log_command;
use crate::macros::info;
use crate::VargoContext;
use crate::VargoResult;

impl VargoNextestRun {
    pub fn add_options(&self, cargo: &mut std::process::Command) {
        dbg!(self);
        cargo.args(["nextest", "run"]);
        cargo.env("VARGO_IN_NEXTEST", "1");

        if self.build_options.release {
            cargo.arg("--release");
        }

        cargo.args(["--package", self.package.as_str()]);

        self.feature_options.add_options(cargo);

        cargo.args(&self.nextest_args);
    }

    fn build_cmd(&self) -> VargoBuild {
        VargoBuild {
            package: None,
            exclude: Default::default(),
            feature_options: self.feature_options.clone(),
            build_options: self.build_options.clone(),
            verus_args: Default::default(),
        }
    }

    fn apply_feature_filter(&mut self) {
        if self.package.as_str() == "rust_verify_test" {
            self.feature_options
                .filter_feature_list(&[VerusFeatures::Singular, VerusFeatures::AxiomUsageInfo]);
        }
    }
}

pub fn nextest_run(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoNextestRun,
) -> VargoResult<()> {
    if vargo_cmd.package != "air" && vargo_cmd.package != "rust_verify_test" {
        return Err(format!(
            "unexpected package for `vargo test`: {}",
            vargo_cmd.package
        ));
    }

    if !context.in_nextest {
        // may need to rebuild rust_verify
        if vargo_cmd.package == "rust_verify_test" {
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
    }

    let mut vargo_cmd = vargo_cmd.clone();
    vargo_cmd.apply_feature_filter();

    let mut cargo = cargo_command(options, context);
    vargo_cmd.add_options(&mut cargo);
    log_command(&cargo, options.vargo_verbose);

    let status = cargo
        .status()
        .map_err(|x| format!("could not execute cargo ({})", x))?;

    if !status.success() {
        return Err(format!(
            "`cargo nextest run` returned status code {:?}",
            status.code()
        ));
    }

    Ok(())
}
