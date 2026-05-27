use cargo_verus::{
    BIN_NAME, ExecutionPlan,
    test_utils::{MockDep, MockPackage, MockWorkspace, VERUS_DRIVER_ARGS, VERUS_DRIVER_ARGS_FOR},
};

fn setup_workspace() -> tempfile::TempDir {
    let optin = "optin".to_string();
    let optout = "optout".to_string();
    let unset = "unset".to_string();
    let hasdeps = "hasdeps".to_string();
    let sibling = "sibling".to_string();

    MockWorkspace::new()
        .members([
            MockPackage::new(&optin).lib().verify(true),
            MockPackage::new(&optout).lib().verify(false),
            MockPackage::new(&unset).lib(),
            MockPackage::new(&hasdeps)
                .lib()
                .deps([
                    MockDep::workspace(&optin),
                    MockDep::workspace(&optout),
                    MockDep::workspace(&unset),
                ])
                .verify(true),
            MockPackage::new(&sibling).lib().verify(true),
        ])
        .materialize()
}

#[test]
fn workspace_explicit_all() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "verify",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--fwd-verus-args-to",
        "all",
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_explicit_roots() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "verify",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--fwd-verus-args-to",
        "roots",
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(!optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_explicit_deps() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "verify",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--fwd-verus-args-to",
        "deps",
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(!hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(!sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_verify_is_all() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "verify",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_build_is_all() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "build",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_check_is_all() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "check",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_focus_is_roots() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";
    let sibling = "sibling";

    let workspace_dir = setup_workspace();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let args = [
        BIN_NAME,
        "focus",
        "--package",
        hasdeps,
        "--package",
        sibling,
        "--",
        "--verify-module=bar",
    ];

    let plan = cargo_verus::plan_execution(Some(workspace_dir.as_path()), args).expect("plan");
    let ExecutionPlan::RunCargo(cargo_plan) = plan else {
        panic!("expected `ExecutionPlan::RunCargo`");
    };

    let driver_args = cargo_plan.parse_driver_args(VERUS_DRIVER_ARGS);
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in {VERUS_DRIVER_ARGS}"
    );

    let hasdeps_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optin}-0.1.0-"));
    assert!(!optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = cargo_plan
        .parse_driver_args_for_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{optout}-0.1.0-"));
    cargo_plan.assert_env_has_no_key_prefix(&format!("{VERUS_DRIVER_ARGS_FOR}{unset}-0.1.0-"));
}
