#[cfg(not(feature = "integration-tests"))]
compile_error!("Enable the `integration-tests` feature to run these tests.");

#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn crate_optin_workdir() {
    let project_dir = clone_fixture(CRATE_OPTIN);
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{}-0.1.0-", CRATE_OPTIN);

    let (status, data) = run_cargo_verus(|cmd| {
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
fn crate_optin_manifest() {
    let project_dir = clone_fixture(CRATE_OPTIN);
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{}-0.1.0-", CRATE_OPTIN);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
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
fn crate_optout_workdir() {
    let project_dir = clone_fixture(CRATE_OPTOUT);

    let (status, data) = run_cargo_verus(|cmd| {
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
fn crate_optout_manifest() {
    let project_dir = clone_fixture(CRATE_OPTOUT);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
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

#[test]
fn crate_unset_workdir() {
    let project_dir = clone_fixture(CRATE_UNSET);

    let (status, data) = run_cargo_verus(|cmd| {
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
fn crate_unset_manifest() {
    let project_dir = clone_fixture(CRATE_UNSET);
    let manifest_path = project_dir.join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
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
