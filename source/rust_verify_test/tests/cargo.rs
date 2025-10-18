#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
use tempfile::tempdir;

#[test] 
fn cargo_new_verifies() {
    // Run cargo verus new in temp_dir
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let args = vec!["new", "--bin", "test_project"];
    let run = run_cargo_verus(&args, temp_dir.path());
    assert!(run.status.success());
    let args = vec!["verify"];
    let run = run_cargo_verus(&args, temp_dir.path().join("test_project").as_path());
    assert!(run.status.success());
}

#[test] 
fn cargo_new_builds() {
    // Run cargo verus new in temp_dir
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let args = vec!["new", "--bin", "test_project"];
    let run = run_cargo_verus(&args, temp_dir.path());
    assert!(run.status.success());
    let args = vec!["build"];
    let run = run_cargo_verus(&args, temp_dir.path().join("test_project").as_path());
    assert!(run.status.success());
}

#[test] 
#[ignore]
fn vstd_macros() {
    let current_exe = std::env::current_exe().unwrap();
    let test_dir = current_exe.parent().unwrap().parent().unwrap().parent().unwrap().parent().unwrap().join("rust_verify_test/tests/cargo-tests");
    let test_dir = test_dir.join("vstd-macros");
    let args = vec!["verify"];
    let run = run_cargo_verus(&args, &test_dir.as_path());
    assert!(run.status.success());
}