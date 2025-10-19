#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
use tempfile::tempdir;
use rust_verify_test_macros::cargo_examples;

fn run_cargo_verus_for_dir(dir: &str) {
    let current_exe = std::env::current_exe().unwrap();
    let test_dir = current_exe.parent().unwrap().parent().unwrap().parent().unwrap().parent().unwrap().join(dir);

    // Don't reuse any artifacts from previous runs
    let args = vec!["clean"];
    let run = run_cargo(&args, &test_dir.as_path());
    assert!(run.status.success());

    let args = vec!["verify"];
    let run = run_cargo_verus(&args, &test_dir.as_path());
    assert!(run.status.success());

    let args = vec!["build"];
    let run = run_cargo_verus(&args, &test_dir.as_path());
    assert!(run.status.success());
}

fn run_vanilla_cargo_for_dir(dir: &str) {
    let current_exe = std::env::current_exe().unwrap();
    let test_dir = current_exe.parent().unwrap().parent().unwrap().parent().unwrap().parent().unwrap().join(dir);

    let args = vec!["clean"];
    let run = run_cargo(&args, &test_dir.as_path());
    assert!(run.status.success());

    let args = vec!["check"];
    let run = run_cargo(&args, &test_dir.as_path());
    assert!(run.status.success());

    let args = vec!["build"];
    let run = run_cargo(&args, &test_dir.as_path());
    assert!(run.status.success());
}

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

// Tests that run `cargo verus {verify, build}` on each crate in the cargo-tests/verified directory
cargo_examples!(true);

// Tests that run `cargo {check, build}` on each crate in the cargo-tests/verified directory
cargo_examples!(false);