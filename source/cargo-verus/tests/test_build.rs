#[path = "src/utils.rs"]
mod utils;

use utils::*;

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

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--expand-errors"));
    assert!(optin_driver_args.contains(&"--rlimit=100"));

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--expand-errors"));
    assert!(hasdeps_driver_args.contains(&"--rlimit=100"));

    data.assert_env_has("RUSTC_WRAPPER");
    data.assert_env_sets("__CARGO_DEFAULT_LIB_METADATA", "verus");
    data.assert_env_sets("__VERUS_DRIVER_VIA_CARGO__", "1");
    data.assert_env_sets_key_prefix(&verify_optin_prefix, "1");
    data.assert_env_sets_key_prefix(&verify_hasdeps_prefix, "1");
    data.assert_env_has_no_key_prefix(&verify_optout_prefix);
    data.assert_env_has_no_key_prefix(&verify_unset_prefix);
}
