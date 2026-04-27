use cargo_verus::{
    BIN_NAME, ExecutionPlan, plan_execution,
    test_utils::{MockPackage, MockWorkspace},
};

#[test]
fn late_package_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--package=foo"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_features_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--features=some-feature"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_all_features_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--all-features"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_no_default_features_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--no-default-features"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_workspace_arg_after_release() {
    let workspace_dir =
        MockWorkspace::new().members([MockPackage::new("foo").lib().verify(true)]).materialize();
    let args = [BIN_NAME, "verify", "--release", "--workspace"];
    let result = plan_execution(Some(workspace_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_frozen_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--frozen"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_locked_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--locked"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_offline_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--offline"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_target_dir_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--target-dir=/tmp/foo"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_config_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "--config=build.jobs=1"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn late_z_flag_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--release", "-Z", "unstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn z_flag_without_space_is_rejected() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "-Zunstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn z_flag_with_space_is_accepted() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "-Z", "unstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);

    // The parser should accept `-Z unstable-options` as properly formatted.
    // On stable toolchains, planning may still fail later when cargo metadata rejects `-Z`.
    if let Err(err) = result {
        let msg = format!("{err:#}");
        assert!(
            !msg.contains("Args forwarded to Cargo must precede args forwarded to Verus"),
            "expected non-parser failure for spaced -Z flag, got: {msg}",
        );
    }
}

#[test]
fn package_before_release_is_ok() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "verify", "--package=foo", "--release"];

    let plan = plan_execution(Some(package_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert!(cargo_plan.args.contains(&"--release".to_string()));
    assert!(
        cargo_plan.args.contains(&"--package".to_string())
            || cargo_plan.args.contains(&"-p".to_string())
    );
}

#[test]
fn features_before_release_is_ok() {
    let package_dir =
        MockPackage::new("foo").lib().verify(true).features(["default=[]"]).materialize();
    let args = [BIN_NAME, "verify", "--features=default", "--release"];

    let plan = plan_execution(Some(package_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert!(cargo_plan.args.contains(&"--release".to_string()));
    assert!(cargo_plan.args.contains(&"--features".to_string()));
}

#[test]
fn focus_late_package_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "focus", "--release", "--package=foo"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn focus_z_flag_without_space_is_rejected() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "focus", "-Zunstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn build_late_package_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "build", "--release", "--package=foo"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn build_z_flag_without_space_is_rejected() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "build", "-Zunstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn check_late_package_arg_after_release() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "check", "--release", "--package=foo"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}

#[test]
fn check_z_flag_without_space_is_rejected() {
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();
    let args = [BIN_NAME, "check", "-Zunstable-options"];
    let result = plan_execution(Some(package_dir.path()), args);
    assert!(result.is_err(), "expected planning to fail for args: {args:?}");
}
