#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;

#[test]
fn verify_single_crate() -> anyhow::Result<()> {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let (mut cmd, data_file) = utils::run_cargo_verus_with_data_file(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });
    let output = cmd.output()?;
    let captured = utils::read_cargo_data(&data_file)?;

    assert!(output.status.success());
    assert_eq!(captured.args, vec!["build"]);
    assert!(captured.env.contains_key("FAKE_CARGO_DATA_FILE"));

    Ok(())
}

#[test]
fn verify_single_crate_explicit_manifest() -> anyhow::Result<()> {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let (mut cmd, data_file) = utils::run_cargo_verus_with_data_file(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(project_dir.join("Cargo.toml"));
    });
    let output = cmd.output()?;
    let captured = utils::read_cargo_data(&data_file)?;

    assert!(output.status.success());
    assert_eq!(
        captured.args,
        vec![
            "build".to_owned(),
            "--manifest-path".to_owned(),
            project_dir.join("Cargo.toml").to_string_lossy().to_string(),
        ]
    );

    Ok(())
}
