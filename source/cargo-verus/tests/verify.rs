#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;

#[test]
fn verify_single_crate() {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let (output, captured) = utils::run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(output.status.success());
    assert_eq!(captured.args, vec!["build"]);
}

#[test]
fn verify_single_crate_explicit_manifest() -> anyhow::Result<()> {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);
    let manifest_path = project_dir.join("Cargo.toml");

    let (output, captured) = utils::run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(output.status.success());
    assert_eq!(
        captured.args,
        vec!["build", "--manifest-path", manifest_path.to_str().expect("manifest path to string")]
    );

    Ok(())
}
