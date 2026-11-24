use std::{env, path::Path};

use cargo_verus::{BIN_NAME, ExecutionPlan, plan_execution};

#[test]
fn known_verus_version_uses_matching_vstd_dep() {
    let expected_vstd_dep = format!("{:?}", "=0.0.0-2026-08-23-0033");

    let args = [
        BIN_NAME,
        "new",
        "--override-verus-version",
        "0.2026.08.23.fbbbbcf",
        "--lib",
        "test-project",
    ];
    let temp_dir = tempfile::tempdir().expect("create temporary dir");
    let plan = plan_execution(&temp_dir, args).expect("plan");
    let ExecutionPlan::CreateNew(creation_plan) = &plan else {
        panic!("expected new-project plan");
    };

    assert_eq!(creation_plan.current_dir, temp_dir.path());
    assert_eq!(creation_plan.name, "test-project");
    assert_eq!(creation_plan.is_bin, false);
    assert_eq!(creation_plan.vstd_dependency, expected_vstd_dep);
}

#[test]
fn dirty_verus_version_uses_path_vstd_dep() {
    let vstd_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("cargo-verus manifest directory has a parent")
        .join("vstd")
        .canonicalize()
        .expect("canonicalize in-tree vstd directory");
    let expected_vstd_dep = format!("{{ path = {vstd_dir:?} }}");

    let args = [
        BIN_NAME,
        "new",
        "--override-verus-version",
        "0.2026.08.23.fbbbbcf.dirty",
        "--bin",
        "test-project",
    ];
    let temp_dir = tempfile::tempdir().expect("create temporary dir");
    let plan = plan_execution(&temp_dir, args).expect("plan");
    let ExecutionPlan::CreateNew(creation_plan) = &plan else {
        panic!("expected new-project plan");
    };

    assert_eq!(creation_plan.current_dir, temp_dir.path());
    assert_eq!(creation_plan.name, "test-project");
    assert_eq!(creation_plan.is_bin, true);
    assert_eq!(creation_plan.vstd_dependency, expected_vstd_dep);
}
