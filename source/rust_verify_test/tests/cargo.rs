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
    target_profile_dir().parent().unwrap().parent().unwrap().join(dir)
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

/// Source for a target containing one trusted item named `name`
fn trusted_item_source(name: &str, with_main: bool) -> String {
    format!(
        "use vstd::prelude::*;\n\
         verus! {{\n\
         #[verus::trusted]\n\
         pub proof fn {name}() {{ assume(true); }}\n\
         }}\n{}",
        if with_main { "fn main() {}\n" } else { "" }
    )
}

/// Run `cargo verus verify --emit-trust-manifests <dir> <cargo_args>` on `project`, returning
/// a map from each manifest's file name to the trusted items it records.
fn emit_trust_manifests(
    project: &std::path::Path,
    cargo_args: &[&str],
) -> std::collections::BTreeMap<String, Vec<String>> {
    let manifest_dir = tempdir().expect("Failed to create temporary manifest directory");
    let manifest_dir_arg = manifest_dir.path().to_string_lossy().into_owned();
    let mut args = vec!["verify", "--emit-trust-manifests", &manifest_dir_arg];
    args.extend(cargo_args);
    let run = run_cargo_verus(&args, project);
    assert!(
        run.status.success(),
        "cargo verus failed:\n{}\n{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );

    // Manifests are written to <manifest dir>/<package id>/<crate name>-<target kind>.json
    let mut manifests = std::collections::BTreeMap::new();
    for package_dir in fs::read_dir(manifest_dir.path()).unwrap() {
        for entry in fs::read_dir(package_dir.unwrap().path()).unwrap() {
            let path = entry.unwrap().path();
            let manifest: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            let names: Vec<String> = manifest["nodes"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|node| node["trust"] == "trusted")
                .map(|node| node["name"].as_str().unwrap().to_owned())
                .collect();
            manifests.insert(path.file_name().unwrap().to_string_lossy().into_owned(), names);
        }
    }
    manifests
}

/// Check that `manifests` consists of exactly the `expected` (file, trusted item) pairs
fn assert_manifests(
    manifests: &std::collections::BTreeMap<String, Vec<String>>,
    expected: &[(&str, &str)],
) {
    let mut expected_files: Vec<&str> = expected.iter().map(|(file, _)| *file).collect();
    expected_files.sort();
    assert_eq!(
        manifests.keys().map(String::as_str).collect::<Vec<_>>(),
        expected_files,
        "unexpected set of manifests: {manifests:#?}"
    );
    for (file, item) in expected {
        assert!(
            manifests[*file].iter().any(|name| name.ends_with(item)),
            "{file} should record `{item}` as trusted: {manifests:#?}"
        );
    }
}

/// Create a `cargo verus new` project named `name`, with `files` (path, contents) replacing or
/// adding to its sources
fn new_project(
    temp_dir: &std::path::Path,
    name: &str,
    kind: &str,
    files: &[(&str, String)],
) -> PathBuf {
    let run = run_cargo_verus(&["new", kind, name], temp_dir);
    assert!(run.status.success());
    let project = temp_dir.join(name);
    adjust_version(project.clone());
    for (path, contents) in files {
        let path = project.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }
    project
}

#[test]
fn cargo_trust_manifests_per_target() {
    // A package with a lib, a bin, an example, and an integration test; each target should get
    // its own trust manifest.
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let project = new_project(
        temp_dir.path(),
        "test_project",
        "--bin",
        &[
            ("src/lib.rs", trusted_item_source("lib_axiom", false)),
            ("src/main.rs", trusted_item_source("bin_axiom", true)),
            ("examples/demo.rs", trusted_item_source("example_axiom", true)),
            ("tests/integration.rs", trusted_item_source("test_axiom", false)),
        ],
    );

    let manifests =
        emit_trust_manifests(&project, &["--lib", "--bins", "--examples", "--test", "integration"]);
    assert_manifests(
        &manifests,
        &[
            ("test_project-lib.json", "lib_axiom"),
            ("test_project-bin.json", "bin_axiom"),
            ("demo-example.json", "example_axiom"),
            ("integration-test.json", "test_axiom"),
        ],
    );

    // With --all-targets, the lib and the bin are also built as unit tests.  They have the same
    // crate name, so their manifests are distinguished by the kind of target they test.
    let manifests = emit_trust_manifests(&project, &["--all-targets"]);
    assert_manifests(
        &manifests,
        &[
            ("test_project-lib.json", "lib_axiom"),
            ("test_project-bin.json", "bin_axiom"),
            ("demo-example.json", "example_axiom"),
            ("integration-test.json", "test_axiom"),
            ("test_project-lib-test.json", "lib_axiom"),
            ("test_project-bin-test.json", "bin_axiom"),
        ],
    );
}

#[test]
fn cargo_trust_manifests_single_target() {
    // A package with only a lib: its unit-test build keeps the plain `-test` suffix.
    let temp_dir = tempdir().expect("Failed to create temporary directory");
    let project = new_project(
        temp_dir.path(),
        "single_lib",
        "--lib",
        &[("src/lib.rs", trusted_item_source("lib_axiom", false))],
    );
    let manifests = emit_trust_manifests(&project, &["--all-targets"]);
    assert_manifests(
        &manifests,
        &[("single_lib-lib.json", "lib_axiom"), ("single_lib-test.json", "lib_axiom")],
    );
}

// Tests that run `cargo verus {verify, build}` on each crate in the cargo-tests/verified directory
cargo_examples!(true);

// Tests that run `cargo {check, build}` on each crate in the cargo-tests/unverified directory
cargo_examples!(false);
