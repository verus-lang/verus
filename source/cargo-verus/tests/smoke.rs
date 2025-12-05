use std::process::Command;

#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;

const FIXTURE_NAME: &str = "foo";

#[test]
fn runs_cargo_verus_with_fake_cargo() {
    let project_dir = utils::clone_fixture(FIXTURE_NAME);

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
