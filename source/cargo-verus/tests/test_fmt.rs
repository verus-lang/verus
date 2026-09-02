use cargo_verus::{
    BIN_NAME, ExecutionPlan, plan_execution,
    test_utils::{MockPackage, MockWorkspace},
};

#[test]
fn detects_cargo_vs_verus() {
    let workspace = MockWorkspace::new()
        .members([
            MockPackage::new("ordinary").lib(),
            MockPackage::new("verus").lib().verify(true),
            MockPackage::new("verus_without_verification").lib().verify(false),
        ])
        .materialize();

    let args = [BIN_NAME, "fmt", "--check"];
    let plan = plan_execution(workspace.path(), args).expect("plan");
    let ExecutionPlan::FormatSources(formatting_plan) = plan else {
        panic!("expected formatting plan");
    };
    let manifest = |package| workspace.path().join(package).canonicalize().expect("canonicalize");

    assert_eq!(formatting_plan.cargo_targets, [manifest("ordinary/Cargo.toml")]);
    assert!(formatting_plan.is_check);
    assert_eq!(
        formatting_plan.verus_targets,
        [manifest("verus/Cargo.toml"), manifest("verus_without_verification/Cargo.toml")]
    );
}
