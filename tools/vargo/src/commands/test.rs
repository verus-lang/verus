use crate::cli::VargoBuild;
use crate::cli::VargoOptions;
use crate::cli::VargoTest;
use crate::cli::VerusFeatures;
use crate::commands::build;
use crate::commands::cargo_command;
use crate::commands::filter_feature_list;
use crate::commands::log_command;
use crate::macros::info;
use crate::VargoContext;
use crate::VargoResult;

impl VargoTest {
    pub fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("test");

        if self.release {
            cargo.arg("--release");
        }

        cargo.args(["--package", self.package.as_str()]);

        if self.no_default_features {
            cargo.arg("--no-default-features");
        }

        for feature in &self.features {
            cargo.arg("--features");
            cargo.arg(format!("{feature}"));
        }

        if let Some(test) = self.testname.as_deref() {
            cargo.arg(test);
        }

        if !self.verus_args.is_empty() {
            // This is to pass arguments to rust_verify_test
            cargo.arg("--");
            // This is to forward arguments to verus
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
            verus_args: self.verus_args.clone(),
        }
    }

    fn apply_feature_filter(&mut self) {
        if self.package.as_str() == "rust_verify_test" {
            self.features = filter_feature_list(
                &self.features,
                [VerusFeatures::Singular, VerusFeatures::AxiomUsageInfo]
                    .into_iter()
                    .collect(),
            );
        }
    }
}

pub fn test(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoTest,
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
                if vargo_cmd.release { " (release)" } else { "" }
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
            "`cargo test` returned status code {:?}",
            status.code()
        ));
    }

    Ok(())
}
