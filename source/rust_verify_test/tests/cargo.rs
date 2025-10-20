#![feature(rustc_private)]
#[macro_use]
mod common;
use std::fs;

use common::*;
use rust_verify_test_macros::cargo_examples;
use tempfile::tempdir;
use toml::Table;

fn compute_test_dir(dir: &str) -> std::path::PathBuf {
    let current_exe = std::env::current_exe().unwrap();
    current_exe.parent().unwrap().parent().unwrap().parent().unwrap().parent().unwrap().join(dir)
}

fn run_cargo_verus_for_dir(dir: &str) {
    let test_dir = compute_test_dir(dir);

    // Check for additional arguments to pass to Verus
    let toml_path = test_dir.join("Cargo.toml");
    let toml = fs::read_to_string(&toml_path)
        .unwrap_or_else(|_| panic!("cannot open Cargo.toml file: {}", toml_path.display()));
    let toml_table = toml.parse::<Table>().unwrap();
    let mut extra_verus_args = vec![];
    if let Some(package) = toml_table.get("package") {
        if let Some(meta) = package.get("metadata") {
            if let Some(verus) = meta.get("verus") {
                if let Some(args) = verus.get("test_args") {
                    if let Some(args) = args.as_str() {
                        extra_verus_args.extend(args.split(" "));
                    }
                }
            }
        }
    }

    // Don't reuse any artifacts from previous runs
    let args = vec!["clean"];
    let run = run_cargo(&args, &test_dir.as_path());
    assert!(run.status.success());

    let mut args = vec!["verify"];
    args.push("--");
    args.extend(&extra_verus_args);
    let run = run_cargo_verus(&args, &test_dir.as_path());
    assert!(run.status.success());

    let mut args = vec!["build"];
    args.push("--");
    args.extend(&extra_verus_args);
    let run = run_cargo_verus(&args, &test_dir.as_path());
    assert!(run.status.success());
}

fn run_vanilla_cargo_for_dir(dir: &str) {
    let test_dir = compute_test_dir(dir);

    // Don't reuse any artifacts from previous runs
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
