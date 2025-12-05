#[cfg(not(feature = "integration-tests"))]
compile_error!("enable the `integration-tests` feature to run these tests");

#[path = "src/utils.rs"]
mod utils;

fn assert_verus_env(data: &utils::CargoData) {
    const VIA_CARGO_ENV: &str = "__VERUS_DRIVER_VIA_CARGO__";
    assert_eq!(
        data.env.get("__CARGO_DEFAULT_LIB_METADATA").map(String::as_str),
        Some("verus"),
        "expected __CARGO_DEFAULT_LIB_METADATA to be set for verus builds"
    );
    assert_eq!(
        data.env.get(VIA_CARGO_ENV).map(String::as_str),
        Some("1"),
        "expected __VERUS_DRIVER_VIA_CARGO__=1"
    );
    assert!(
        data.env.contains_key("RUSTC_WRAPPER"),
        "RUSTC_WRAPPER should point to the verus driver"
    );
    assert!(
        data.env.keys().any(|k| k.starts_with("__VERUS_DRIVER_VERIFY_")),
        "expected a __VERUS_DRIVER_VERIFY_* flag for verifying the package"
    );
}

#[test]
fn verify_single_crate() {
    let project_dir = utils::clone_fixture(utils::SINGLE_CRATE);

    let (status, captured) = utils::run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("verify");
    });

    assert!(status.success());
    assert_eq!(captured.args, vec!["build"]);
    assert_verus_env(&captured);
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
    assert_verus_env(&captured);

    Ok(())
}
