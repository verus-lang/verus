#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn lib_with_example_imports_own_lib() {
    let package_name = "mylib";
    let args_prefix = format!(" __VERUS_DRIVER_ARGS_FOR_{package_name}-0.1.0-");

    let project_dir = MockPackage::new(package_name)
        .lib()
        .example("foo")
        .verify(true)
        .materialize();

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("build");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args_for_key_prefix(&args_prefix);
    assert!(
        driver_args.contains(&"import-dep-if-present=mylib"),
        "driver args should include the package's own lib: {:?}",
        driver_args,
    );
}

#[test]
fn bin_only_no_own_lib_import() {
    let package_name = "mybin";
    let args_prefix = format!(" __VERUS_DRIVER_ARGS_FOR_{package_name}-0.1.0-");

    let project_dir = MockPackage::new(package_name)
        .bin("main")
        .verify(true)
        .materialize();

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&project_dir).arg("build");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args_for_key_prefix(&args_prefix);
    assert!(
        !driver_args.contains(&"import-dep-if-present=mybin"),
        "driver args should not import a lib for a bin-only package: {:?}",
        driver_args,
    );
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
        cmd.current_dir(&workspace_dir).arg("build");
        cmd.arg("--release");
        cmd.arg("--");
        cmd.arg("--expand-errors");
        cmd.arg("--rlimit=100");
    });

    assert!(status.success());
    assert_eq!(data.args, vec!["build", "--release"]);

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(driver_args.contains(&"--expand-errors"));
    assert!(driver_args.contains(&"--rlimit=100"));

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
