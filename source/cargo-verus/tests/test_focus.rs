use cargo_verus::{
    BIN_NAME, ExecutionPlan,
    test_utils::{
        CARGO_DEFAULT_LIB_METADATA, MockDep, MockPackage, MockWorkspace, RUSTC_WRAPPER,
        VERUS_DRIVER_ARGS, VERUS_DRIVER_ARGS_FOR, VERUS_DRIVER_VERIFY, VERUS_DRIVER_VIA_CARGO,
    },
};

#[test]
fn crate_optin_manifest() {
    let crate_name = "foo";
    let verify_crate_prefix = format!("{VERUS_DRIVER_VERIFY}{crate_name}-0.1.0-");
    let verify_for_crate_prefix = format!("{VERUS_DRIVER_ARGS_FOR}{crate_name}-0.1.0-");
    let package_dir = MockPackage::new(crate_name).lib().verify(true).materialize();

    let package_dir = package_dir.path().canonicalize().expect("canonical path");
    let manifest_path = package_dir.join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "focus", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let target_dir = package_dir.join("target").join("verus-partial");
    let target_dir = target_dir.to_str().expect("target dir to string");

    assert_eq!(
        cargo_plan.args,
        ["check", "--manifest-path", manifest_path, "--target-dir", target_dir],
    );

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");
    cargo_plan.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
    cargo_plan.assert_env_has_no_key_prefix(&verify_for_crate_prefix);
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

    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.join("Cargo.toml");
    let manifest_path = manifest_path.to_str().expect("manifest path to string");

    let args = [BIN_NAME, "focus", "--manifest-path", manifest_path];

    let plan = cargo_verus::plan_execution(None, args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let target_dir = workspace_dir.join("target").join("verus-partial");
    let target_dir = target_dir.to_str().expect("target dir to string");

    assert_eq!(
        cargo_plan.args,
        ["check", "--manifest-path", manifest_path, "--target-dir", target_dir],
    );

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");

    cargo_plan.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    let verify_hasdeps_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(!verify_hasdeps_args.contains(&"--no-verify"));

    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    let verify_optin_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(!verify_optin_args.contains(&"--no-verify"));

    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_package_hasdeps() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps)
                .lib()
                .deps([MockDep::workspace(optin), MockDep::workspace(optout)])
                .verify(true),
        ])
        .materialize();

    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let verify_optin_prefix = format!("{VERUS_DRIVER_VERIFY}{optin}-0.1.0-");
    let verify_optout_prefix = format!("{VERUS_DRIVER_VERIFY}{optout}-0.1.0-");
    let verify_unset_prefix = format!("{VERUS_DRIVER_VERIFY}{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("{VERUS_DRIVER_VERIFY}{hasdeps}-0.1.0-");

    let args = [BIN_NAME, "focus", "--package", hasdeps];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let target_dir = workspace_dir.join("target").join("verus-partial");
    let target_dir = target_dir.to_str().expect("target dir to string");

    assert_eq!(cargo_plan.args, ["check", "--target-dir", target_dir, "--package", hasdeps],);

    cargo_plan.assert_env_has(RUSTC_WRAPPER);
    cargo_plan.assert_env_sets(CARGO_DEFAULT_LIB_METADATA, "verus");
    cargo_plan.assert_env_sets(VERUS_DRIVER_VIA_CARGO, "1");

    cargo_plan.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    let verify_hasdeps_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(!verify_hasdeps_args.contains(&"--no-verify"));

    cargo_plan.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    let verify_optin_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(verify_optin_args.contains(&"--no-verify"));

    cargo_plan.assert_env_has_no_key_prefix(&verify_optout_prefix);
    cargo_plan.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_package_hasdeps_forwards_verus_args_only_to_roots() {
    let optin = "optin";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [BIN_NAME, "focus", "--package", hasdeps, "--", "--verify-module=bar"];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let root_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(
        root_driver_args.contains(&"--verify-module=bar"),
        "expected root crate to receive --verify-module=bar, got: {:?}",
        root_driver_args
    );

    let dep_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(
        !dep_driver_args.contains(&"--verify-module=bar"),
        "dependency should not receive --verify-module=bar, got: {:?}",
        dep_driver_args
    );
}
