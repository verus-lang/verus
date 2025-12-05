#[cfg(not(feature = "integration-tests"))]
compile_error!("Enable the `integration-tests` feature to run these tests.");

#[path = "src/utils.rs"]
mod utils;

#[test]
fn workdir_single_optin() {
    let project_dir = utils::clone_fixture(utils::SINGLE_OPTIN);
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{}-0.1.0-", utils::SINGLE_OPTIN);

    let (status, data) = utils::run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(status.success());

    assert_eq!(data.args, vec!["build"]);

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
}

#[test]
fn manifest_single_optin() {
    let project_dir = utils::clone_fixture(utils::SINGLE_OPTIN);
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{}-0.1.0-", utils::SINGLE_OPTIN);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, data) = utils::run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());

    assert_eq!(
        data.args,
        vec!["build", "--manifest-path", manifest_path.to_str().expect("manifest path to string")]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
}

#[test]
fn workdir_single_optout() {
    let project_dir = utils::clone_fixture(utils::SINGLE_OPTOUT);

    let (status, data) = utils::run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(status.success());

    assert_eq!(data.args, vec!["build"]);

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_has_no_key_prefix("__VERUS_DRIVER_VERIFY_");
}

#[test]
fn manifest_single_optout() {
    let project_dir = utils::clone_fixture(utils::SINGLE_OPTOUT);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, data) = utils::run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());

    assert_eq!(
        data.args,
        vec!["build", "--manifest-path", manifest_path.to_str().expect("manifest path to string")]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_has_no_key_prefix("__VERUS_DRIVER_VERIFY_");
}
