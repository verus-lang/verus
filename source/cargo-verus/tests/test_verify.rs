use cargo_verus::{
    BIN_NAME, ExecutionPlan,
    test_utils::{
        CARGO_DEFAULT_LIB_METADATA, MockDep, MockPackage, MockWorkspace, RUSTC_WRAPPER,
        VERUS_DRIVER_VERIFY, VERUS_DRIVER_VIA_CARGO,
    },
};

#[test]
fn crate_optin_workdir() {
    let package_name = "foo";
    let verify_crate_prefix = format!("{VERUS_DRIVER_VERIFY}{package_name}-0.1.0-");
    let project_dir = MockPackage::new(package_name).lib().verify(true).materialize();

    let args = [BIN_NAME, "verify"];

    let plan = cargo_verus::plan_execution(Some(project_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check"]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
}

#[test]
fn crate_optin_manifest() {
    let package_name = "foo";
    let verify_crate_prefix = format!("{VERUS_DRIVER_VERIFY}{package_name}-0.1.0-");
    let package_dir = MockPackage::new(package_name).lib().verify(true).materialize();

    let manifest_path = package_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
}

#[test]
fn crate_optout_workdir() {
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().verify(false).materialize();

    let args = [BIN_NAME, "verify"];

    let plan = cargo_verus::plan_execution(Some(package_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check"]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_has_no_key_prefix(VERUS_DRIVER_VERIFY);
}

#[test]
fn crate_optout_manifest() {
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().verify(false).materialize();
    let manifest_path = package_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_has_no_key_prefix(VERUS_DRIVER_VERIFY);
}

#[test]
fn crate_unset_workdir() {
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().materialize();

    let args = [BIN_NAME, "verify"];

    let plan = cargo_verus::plan_execution(Some(package_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check"]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_has_no_key_prefix(VERUS_DRIVER_VERIFY);
}

#[test]
fn crate_unset_manifest() {
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().materialize();

    let manifest_path = package_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_has_no_key_prefix(VERUS_DRIVER_VERIFY);
}

#[test]
fn workspace_workdir() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let args = [BIN_NAME, "verify"];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check"]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_manifest() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_manifest_package_optin() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path, "--package", optin];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path, "--package", optin]);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_hasdeps_prefix);
}

#[test]
fn workspace_manifest_package_hasdeps() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "verify", "--manifest-path", manifest_path, "--package", hasdeps];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    assert_eq!(cargo_plan.args, ["check", "--manifest-path", manifest_path, "--package", hasdeps],);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
