use crate::cli::VargoBuild;
use crate::cli::VargoOptions;
use crate::cli::VargoTest;
use crate::cli::VerusFeatures;
use crate::commands::build;
use crate::commands::cargo_run;
use crate::commands::AddOptions;
use crate::macros::info;
use crate::VargoContext;

impl AddOptions for VargoTest {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("test");

        if self.build_options.release {
            cargo.arg("--release");
        }

        cargo.args(["--package", self.package.as_str()]);

        self.feature_options.add_options(cargo);

        cargo.args(&self.test_args);
    }

    fn cmd_name(&self) -> &str {
        "test"
    }
}

impl VargoTest {
    fn build_cmd(&self) -> VargoBuild {
        VargoBuild {
            package: None,
            exclude: Default::default(),
            feature_options: self.feature_options.clone(),
            build_options: self.build_options.clone(),
            verus_args: Default::default(),
        }
    }

    /// Filter features based on the supported features for the packages
    fn apply_feature_filter(&mut self) {
        if self.package.as_str() == "rust_verify_test" {
            self.feature_options
                .filter_feature_list(&[VerusFeatures::Singular]);
        }
    }
}

pub fn test(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoTest,
) -> anyhow::Result<()> {
    if vargo_cmd.package != "air" && vargo_cmd.package != "rust_verify_test" {
        anyhow::bail!("unexpected package for `vargo test`: {}", vargo_cmd.package);
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

    cargo_run(options, context, &vargo_cmd)
}
