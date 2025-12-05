#[cfg(not(feature = "integration-tests"))]
compile_error!("Enable the `integration-tests` feature to run these tests.");

#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn crate_optin_workdir() {
    let project_dir = clone_fixture(CRATE_OPTIN);
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{CRATE_OPTIN}-0.1.0-");

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
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{CRATE_OPTIN}-0.1.0-");
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

#[test]
fn workspace_workdir() {
    let project_dir = clone_fixture("workspace");
    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTIN}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTOUT}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_UNSET}-0.1.0-");
    let verify_with_deps_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_HASDEPS}-0.1.0-");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(status.success());
    assert_eq!(data.args, vec!["build"]);

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_with_deps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_manifest() {
    let project_dir = clone_fixture("workspace");
    let manifest_path = project_dir.join("Cargo.toml");
    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTIN}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTOUT}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_UNSET}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_HASDEPS}-0.1.0-");

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
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_manifest_package_optin() {
    let project_dir = clone_fixture("workspace");
    let manifest_path = project_dir.join("Cargo.toml");
    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTIN}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTOUT}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_UNSET}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_HASDEPS}-0.1.0-");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--package").arg(MEMBER_OPTIN);
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());
    assert_eq!(
        data.args,
        vec![
            "build",
            "--package",
            MEMBER_OPTIN,
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string")
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
    data.assert_env_has_no_key_prefix(&verify_hasdeps_prefix);
}

#[test]
fn workspace_manifest_package_hasdeps() {
    let project_dir = clone_fixture("workspace");
    let manifest_path = project_dir.join("Cargo.toml");
    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTIN}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_OPTOUT}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_UNSET}-0.1.0-");
    let verify_with_deps_prefix = format!("__VERUS_DRIVER_VERIFY_{MEMBER_HASDEPS}-0.1.0-");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--package").arg(MEMBER_HASDEPS);
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());
    assert_eq!(
        data.args,
        vec![
            "build",
            "--package",
            MEMBER_HASDEPS,
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string")
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_with_deps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
