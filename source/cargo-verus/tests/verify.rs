#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;

#[test]
fn verify_single_crate() {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let output = utils::run_cargo_verus()
        .arg("verify")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
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
