#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn crate_optin_workdir() {
    let package_name = "foo";
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{package_name}-0.1.0-");
    let project_dir = MockPackage::new(package_name).lib().verify(true).materialize();

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
    let package_name = "foo";
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{package_name}-0.1.0-");
    let package_dir = MockPackage::new(package_name).lib().verify(true).materialize();

    let manifest_path = package_dir.path().join("Cargo.toml");

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
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().verify(false).materialize();

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
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
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().verify(false).materialize();
    let manifest_path = package_dir.path().join("Cargo.toml");

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
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().materialize();

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
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
    let package_name = "foo";
    let package_dir = MockPackage::new(package_name).lib().materialize();

    let manifest_path = package_dir.path().join("Cargo.toml");

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
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&workspace_dir).arg("verify");
    });

    assert!(status.success());
    assert_eq!(data.args, vec!["build"]);

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_manifest() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");

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
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
        cmd.arg("--package").arg(optin);
    });

    assert!(status.success());
    assert_eq!(
        data.args,
        vec![
            "build",
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string"),
            "--package",
            optin,
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
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps).lib().deps([MockDep::workspace(optin)]).verify(true),
        ])
        .materialize();

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("verify");
        cmd.arg("--manifest-path").arg(&manifest_path);
        cmd.arg("--package").arg(hasdeps);
    });

    assert!(status.success());
    assert_eq!(
        data.args,
        vec![
            "build",
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string"),
            "--package",
            hasdeps,
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
