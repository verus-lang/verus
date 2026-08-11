#![feature(rustc_private)]
#[macro_use]
mod common;
use std::fs;

use common::*;
use rust_verify_test_macros::cargo_examples;
use std::path::PathBuf;
use tempfile::tempdir;
use toml::{Table, Value};

fn compute_test_dir(dir: &str) -> std::path::PathBuf {
    let current_exe = std::env::current_exe().unwrap();
    current_exe.parent().unwrap().parent().unwrap().parent().unwrap().parent().unwrap().join(dir)
}

fn parse_toml_file(path: &std::path::Path) -> Table {
    let toml_content = fs::read_to_string(path)
        .unwrap_or_else(|_| panic!("cannot open Cargo.toml file: {}", path.display()));
    toml_content.parse::<Table>().unwrap()
}

fn find_verus_config<'a>(table: &'a Table, entry: &str) -> Option<&'a str> {
    if let Some(package) = table.get("package") {
        if let Some(meta) = package.get("metadata") {
            if let Some(verus) = meta.get("verus") {
                if let Some(value) = verus.get(entry) {
                    if value.is_bool() {
                        return Some(if value.as_bool().unwrap() { "true" } else { "false" });
                    } else if value.is_str() {
                        return Some(value.as_str().unwrap());
                    } else {
                        return None;
                    }
                }
            }
        }
    }
    None
}

fn run_cargo_verus_for_dir(dir: &str) {
    let test_dir = compute_test_dir(dir);

    // Check for additional Verus-related metadata
    let toml_path = test_dir.join("Cargo.toml");
    let toml_table = parse_toml_file(&toml_path);

    // See if this test is currently being ignored
    let ignore = find_verus_config(&toml_table, "test_ignore").map_or(false, |v| v == "true");
    if ignore {
        eprintln!("Ignoring cargo verus test in {}", dir);
        return;
    }

    // Check for extra verus args
    let mut extra_verus_args = vec![];
    if let Some(args) = find_verus_config(&toml_table, "test_args") {
        extra_verus_args.extend(args.split(" "));
    }

    // Use a temp dir for the target dir to isolate each test run
    let target_dir = tempdir().expect("Failed to create temporary target directory");

    let mut args = vec!["verify"];
    args.push("--");
    args.extend(&extra_verus_args);
    let run = run_cargo_verus_with_target(&args, &test_dir, target_dir.path());
    assert!(run.status.success());

    let mut args = vec!["build"];
    args.push("--");
    args.extend(&extra_verus_args);
    let run = run_cargo_verus_with_target(&args, &test_dir, target_dir.path());
    assert!(run.status.success());
}

fn run_vanilla_cargo_for_dir(dir: &str) {
    let test_dir = compute_test_dir(dir);

    // Check for additional Verus-related metadata
    let toml_path = test_dir.join("Cargo.toml");
    let toml_table = parse_toml_file(&toml_path);

    // See if this test is currently being ignored
    let ignore = find_verus_config(&toml_table, "test_ignore").map_or(false, |v| v == "true");
    if ignore {
        eprintln!("Ignoring cargo verus test in {}", dir);
        return;
    }

    // Use a temp dir for the target dir to isolate each test run
    let target_dir = tempdir().expect("Failed to create temporary target directory");

    let args = vec!["check"];
    let run = run_cargo_with_target(&args, &test_dir, target_dir.path());
    assert!(run.status.success());

    let args = vec!["build"];
    let run = run_cargo_with_target(&args, &test_dir, target_dir.path());
    assert!(run.status.success());
}

// If vstd is modified as part of a change, the tests should use the local
// version rather than what's on crates.io. This is not a great solution to
// handle this though..
fn adjust_version(mut project_path: PathBuf) {
    project_path.push("Cargo.toml");
    let mut toml_table = parse_toml_file(&project_path);
    let Some(Value::Table(dependencies)) = toml_table.get_mut("dependencies") else {
        panic!("no dependencies");
    };
    let Some(version) = dependencies.get_mut("vstd") else {
        panic!("no vstd version");
    };
    let mut cur_file = std::env::current_dir().expect("current dir");
    cur_file.pop();
    cur_file.push("vstd");

    let mut new_vstd_entry = Table::new();
    new_vstd_entry.insert(
        "path".to_string(),
        Value::String(cur_file.to_str().expect("valid unicode path").to_owned()),
    );
    *version = Value::Table(new_vstd_entry);
    std::fs::write(project_path, toml_table.to_string()).expect("write toml");
}

#[test]
fn cargo_new_verifies() {
    // Run cargo verus new in temp_dir
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let args = vec!["new", "--bin", "test_project"];
    let temp_dir_path = temp_dir.path().to_owned();
    // replace above line by this to debug this test:
    // let temp_dir_path = temp_dir.keep();
    let run = run_cargo_verus(&args, &temp_dir_path);
    let mut project_path = temp_dir_path.clone();
    project_path.push("test_project");
    adjust_version(project_path);
    assert!(run.status.success());
    let args = vec!["verify"];
    let run = run_cargo_verus(&args, temp_dir_path.join("test_project").as_path());
    assert!(run.status.success());
}

#[test]
fn cargo_new_builds() {
    // Run cargo verus new in temp_dir
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let args = vec!["new", "--bin", "test_project"];
    let run = run_cargo_verus(&args, temp_dir.path());
    adjust_version(temp_dir.path().join("test_project"));
    assert!(run.status.success());
    let args = vec!["build"];
    let run = run_cargo_verus(&args, temp_dir.path().join("test_project").as_path());
    assert!(run.status.success());
}

#[test]
fn cargo_partial_verification_is_not_reused_as_full_verification() {
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let run = run_cargo_verus(&["new", "--bin", "partial_verification"], temp_dir.path());
    assert!(
        run.status.success(),
        "cargo verus new failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );

    let project_dir = temp_dir.path().join("partial_verification");
    adjust_version(project_dir.clone());
    let source_dir = project_dir.join("src");
    fs::write(
        source_dir.join("main.rs"),
        r#"use vstd::prelude::*;

mod b;

verus! {

fn check_value() {
    assert(b::value() == 1);
}

}

fn main() {}
"#,
    )
    .expect("write main.rs");
    let b_path = source_dir.join("b.rs");
    fs::write(
        &b_path,
        r#"use vstd::prelude::*;

verus! {

pub open spec fn value() -> int {
    1
}

}
"#,
    )
    .expect("write b.rs");

    let target_dir = temp_dir.path().join("target");
    let run = run_cargo_verus_with_target(&["verify"], &project_dir, &target_dir);
    assert!(
        run.status.success(),
        "initial verification failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );

    fs::write(
        b_path,
        r#"use vstd::prelude::*;

verus! {

pub open spec fn value() -> int {
    2
}

}
"#,
    )
    .expect("update b.rs");

    let run = run_cargo_verus_with_target(
        &["verify", "--fwd-verus-args-to", "roots", "--", "--verify-module", "b"],
        &project_dir,
        &target_dir,
    );
    assert!(
        run.status.success(),
        "partial verification failed:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );

    let run = run_cargo_verus_with_target(&["verify"], &project_dir, &target_dir);
    assert!(
        !run.status.success(),
        "full verification improperly reused the partial verification result"
    );
    assert!(
        String::from_utf8_lossy(&run.stderr).contains("assertion failed"),
        "full verification failed unexpectedly:\n{}",
        String::from_utf8_lossy(&run.stderr),
    );
}

// Tests that run `cargo verus {verify, build}` on each crate in the cargo-tests/verified directory
cargo_examples!(true);

// Tests that run `cargo {check, build}` on each crate in the cargo-tests/unverified directory
cargo_examples!(false);
