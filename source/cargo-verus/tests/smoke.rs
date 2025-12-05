use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

const FIXTURE_MANIFEST: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/foo/Cargo.toml");

#[test]
fn runs_cargo_verus_with_fake_cargo() {
    let mut project_dir = env::temp_dir();
    project_dir.push(format!("cargo-verus-tests-{}", std::process::id()));
    let _ = fs::remove_dir_all(&project_dir);
    fs::create_dir_all(project_dir.join("src")).expect("failed to create temp project dir");
    fs::copy(Path::new(FIXTURE_MANIFEST), project_dir.join("Cargo.toml"))
        .expect("failed to copy fixture manifest");
    fs::write(project_dir.join("src").join("main.rs"), "fn main() {}\n")
        .expect("failed to write temp main.rs");

    let output = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"))
        .arg("verify")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .env("CARGO", assert_cmd::cargo::cargo_bin!("fake-cargo"))
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
