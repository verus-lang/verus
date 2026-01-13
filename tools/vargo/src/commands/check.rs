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
    fn cmd_for_package(&self, package: &str) -> Self {
        let mut cpy = self.clone();
        cpy.package = Some(package.to_owned());
        cpy.apply_feature_filter();
        cpy
    }

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
    const PACKAGES: &[&str] = &[
        "air",
        "cargo-verus",
        "rust_verify",
        "verus",
        "verus_builtin",
        "verus_builtin_macros",
        "verusdoc",
        "verus_state_machines_macros",
        "vstd_build",
    ];

    if context.in_nextest {
        return Ok(());
    }

    if vargo_cmd.package.is_some() {
        let mut vargo_cmd = vargo_cmd.clone();
        vargo_cmd.apply_feature_filter();
        check_target(options, context, &vargo_cmd)?;
    } else {
        for package in PACKAGES.iter().filter(|p| !vargo_cmd.exclude.contains(**p)) {
            let vargo_cmd = vargo_cmd.cmd_for_package(package);
            check_target(options, context, &vargo_cmd)?;
        }
    }

    Ok(())
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
