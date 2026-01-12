#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn crate_optin_manifest() {
    let crate_name = "foo";
    let verify_crate_prefix = format!("__VERUS_DRIVER_VERIFY_{crate_name}-0.1.0-");
    let verify_for_crate_prefix = format!(" __VERUS_DRIVER_ARGS_FOR_{crate_name}-0.1.0-");
    let package_dir = MockPackage::new(crate_name).lib().verify(true).materialize();

    // Canonicalize the path to avoid weirdness on e.g. macOS
    let package_dir = package_dir.path().canonicalize().expect("canonical path");

    let manifest_path = package_dir.join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("focus");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());

    let target_dir = package_dir.join("target").join("verus-partial");

    assert_eq!(
        data.args,
        vec![
            "build",
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string"),
            "--target-dir",
            target_dir.to_str().expect("target dir to string"),
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_crate_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_for_crate_prefix);
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

    // Canonicalize the path to avoid weirdness on e.g. macOS
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("focus");
        cmd.arg("--manifest-path").arg(&manifest_path);
    });

    assert!(status.success());

    let target_dir = workspace_dir.join("target").join("verus-partial");

    assert_eq!(
        data.args,
        vec![
            "build",
            "--manifest-path",
            manifest_path.to_str().expect("manifest path to string"),
            "--target-dir",
            target_dir.to_str().expect("target dir to string"),
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");

    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    let verify_hasdeps_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(!verify_hasdeps_args.contains(&"--no-verify"));

    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    let verify_optin_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(!verify_optin_args.contains(&"--no-verify"));

    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}

#[test]
fn workspace_package_hasdeps() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(optin).lib().verify(true),
            MockPackage::new(optout).lib().verify(false),
            MockPackage::new(unset).lib(),
            MockPackage::new(hasdeps)
                .lib()
                .deps([MockDep::workspace(optin), MockDep::workspace(optout)])
                .verify(true),
        ])
        .materialize();

    // Canonicalize the path to avoid weirdness on e.g. macOS
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&workspace_dir);
        cmd.arg("focus");
        cmd.arg("--package").arg(hasdeps);
    });

    assert!(status.success());

    let target_dir = workspace_dir.join("target").join("verus-partial");

    assert_eq!(
        data.args,
        vec![
            "build",
            "--target-dir",
            target_dir.to_str().expect("target dir to string"),
            "--package",
            "hasdeps",
        ]
    );

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");

    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    let verify_hasdeps_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(!verify_hasdeps_args.contains(&"--no-verify"));

    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    let verify_optin_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(verify_optin_args.contains(&"--no-verify"));

    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
