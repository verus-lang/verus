#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn workspace_manifest_package_hasdeps() {
    let optin = "optin";
    let optout = "optout";
    let unset = "unset";
    let hasdeps = "hasdeps";

    let workspace_dir = MockWorkspace::new()
        .member(MockPackage::new(optin).lib().verify(true))
        .member(MockPackage::new(optout).lib().verify(false))
        .member(MockPackage::new(unset).lib())
        .member(MockPackage::new(hasdeps).lib().dep(optin).verify(true))
        .materialize();

    let verify_optin_prefix = format!("__VERUS_DRIVER_VERIFY_{optin}-0.1.0-");
    let verify_optout_prefix = format!("__VERUS_DRIVER_VERIFY_{optout}-0.1.0-");
    let verify_unset_prefix = format!("__VERUS_DRIVER_VERIFY_{unset}-0.1.0-");
    let verify_hasdeps_prefix = format!("__VERUS_DRIVER_VERIFY_{hasdeps}-0.1.0-");

    let manifest_path = workspace_dir.path().join("Cargo.toml");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.arg("focus");
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
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optin_prefix);
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
