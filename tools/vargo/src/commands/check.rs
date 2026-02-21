use crate::cli::VargoCheck;
use crate::cli::VargoOptions;
use crate::cli::VerusFeatures;
use crate::commands::cargo_run;
use crate::commands::AddOptions;
use crate::context::VargoContext;
use crate::macros::info;

impl AddOptions for VargoCheck {
    fn add_options(&self, cargo: &mut std::process::Command) {
        cargo.arg("check");

        if self.release {
            cargo.arg("--release");
        }

        if let Some(p) = self.package.as_deref() {
            cargo.args(["--package", p]);
        } else {
            cargo.arg("--workspace");
        }

        for exclude in &self.exclude {
            let e = exclude.as_str();
            cargo.args(["--exclude", e]);
        }

        self.feature_options.add_options(cargo);
    }

    fn cmd_name(&self) -> &str {
        "check"
    }
}

impl VargoCheck {
    fn apply_feature_filter(&mut self) {
        match self.package.as_deref() {
            Some("rust_verify") => {
                self.feature_options
                    .filter_feature_list(&[VerusFeatures::Singular]);
            }
            Some("verus") => {
                self.feature_options
                    .filter_feature_list(&[VerusFeatures::RecordHistory]);
            }
            _ => {
                self.feature_options.features = Vec::new();
            }
        }
    }
}

pub fn check(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoCheck,
) -> anyhow::Result<()> {
    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.is_some() {
        let mut vargo_cmd = vargo_cmd.clone();
        vargo_cmd.apply_feature_filter();
        check_target(options, context, &vargo_cmd)
    } else {
        info!("running cargo-check",);
        cargo_run(options, context, vargo_cmd)
    }
}

fn check_target(
    options: &VargoOptions,
    context: &VargoContext,
    vargo_cmd: &VargoCheck,
) -> anyhow::Result<()> {
    assert!(vargo_cmd.package.is_some());
    info!(
        "running cargo-check on {}",
        vargo_cmd
            .package
            .as_deref()
            .expect("when building a particular target, package is set")
    );
    cargo_run(options, context, vargo_cmd)
}
