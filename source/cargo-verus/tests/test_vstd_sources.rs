use std::{fs, path::PathBuf};

use cargo_verus::test_utils::{MockDep, MockPackage, MockWorkspace};

const VERUS_GITHUB_URL: &str = "https://github.com/verus-lang/verus";
const VERUS_GITHUB_COMMIT: &str = "cd03505";
const VSTD_VERSION: &str = "0.0.0-2026-05-31-0205";

#[test]
fn constructs_workspace_with_vstd_registry_git_and_path_dependencies() {
    let workspace = MockWorkspace::new()
        .members([
            MockPackage::new("consumer").lib().deps([
                MockDep::registry("vstd", VSTD_VERSION).alias("vstd_registry"),
                MockDep::git("vstd", VERUS_GITHUB_URL, VERUS_GITHUB_COMMIT).alias("vstd_git"),
                MockDep::path("vstd", "../fake-vstd").alias("vstd_path"),
                MockDep::workspace("vstd").alias("vstd_workspace"),
            ]),
            MockPackage::new("fake-vstd").lib(),
        ])
        .materialize();

    print_cargo_toml(workspace.path().join("Cargo.toml"));
    print_cargo_toml(workspace.path().join("consumer").join("Cargo.toml"));
    print_cargo_toml(workspace.path().join("fake-vstd").join("Cargo.toml"));
}

fn print_cargo_toml(path: PathBuf) {
    let contents = fs::read_to_string(&path).unwrap_or_else(|_| panic!("read {path:?}"));
    println!("== {} ==\n{contents}", path.display());
}
