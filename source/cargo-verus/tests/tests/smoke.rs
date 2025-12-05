use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use assert_cmd::cargo::cargo_bin;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_path_buf()
}

fn target_dir() -> PathBuf {
    env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| workspace_root().join("target"))
}

fn cargo_verus_bin() -> PathBuf {
    let status = Command::new("cargo")
        .args(["build", "-p", "cargo-verus"])
        .current_dir(workspace_root())
        .status()
        .expect("failed to build cargo-verus");
    assert!(status.success(), "building cargo-verus failed");

    let mut path = target_dir().join("debug").join("cargo-verus");
    if cfg!(windows) {
        path.set_extension("exe");
    }
    path
}

fn fake_cargo_bin() -> PathBuf {
    cargo_bin("fake-cargo")
}

#[test]
fn runs_cargo_verus_with_fake_cargo() {
    let fixture =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures").join("foo").join("Cargo.toml");

    let mut project_dir = env::temp_dir();
    project_dir.push(format!("cargo-verus-tests-{}", std::process::id()));
    let _ = fs::remove_dir_all(&project_dir);
    fs::create_dir_all(project_dir.join("src")).expect("failed to create temp project dir");
    fs::copy(&fixture, project_dir.join("Cargo.toml")).expect("failed to copy fixture manifest");
    fs::write(project_dir.join("src").join("main.rs"), "fn main() {}\n")
        .expect("failed to write temp main.rs");

    let output = Command::new(cargo_verus_bin())
        .arg("verify")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .env("CARGO", fake_cargo_bin())
        .output()
        .expect("failed to run cargo-verus");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "cargo-verus did not succeed\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("FAKE-CARGO"), "fake-cargo output missing in stdout:\n{stdout}");
}
