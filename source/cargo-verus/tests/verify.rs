#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;
use utils::assert_verus_command_env;

#[test]
fn verify_single_crate() {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let (status, captured) = utils::run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(status.success());
    assert_eq!(captured.args, vec!["build"]);
    assert_verus_command_env(&captured);
    assert!(
        captured.env.keys().any(|k| k.starts_with("__VERUS_DRIVER_VERIFY_")),
        "expected a __VERUS_DRIVER_VERIFY_* flag for verifying the package"
    );
}

#[test]
fn verify_single_crate_explicit_manifest() -> anyhow::Result<()> {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, captured) = utils::run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());
    assert_eq!(
        captured.args,
        vec!["build", "--manifest-path", manifest_path.to_str().expect("manifest path to string")]
    );
    assert_verus_command_env(&captured);
    assert!(
        captured.env.keys().any(|k| k.starts_with("__VERUS_DRIVER_VERIFY_")),
        "expected a __VERUS_DRIVER_VERIFY_* flag for verifying the package"
    );

    Ok(())
}
