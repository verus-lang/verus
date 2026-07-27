use std::process::ExitCode;

use cargo_verus::{BIN_NAME, ExecutionPlan, execute_plan, plan_execution};

#[test]
fn toolchain_list_plans_and_executes() {
    let current_dir = tempfile::tempdir().expect("create temp dir");
    let args = [BIN_NAME, "toolchain", "list"];
    let plan = plan_execution(current_dir.path(), args).expect("plan");
    let ExecutionPlan::ListToolchains = plan else {
        panic!("expected `ExecutionPlan::ListToolchains`");
    };

    let exit_code = execute_plan(&plan).expect("execute");
    assert_eq!(exit_code, ExitCode::SUCCESS);
}
