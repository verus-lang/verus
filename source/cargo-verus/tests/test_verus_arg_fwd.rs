#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn fwd_verus_args_to_all() {
    let optin = "optin".to_string();
    let optout = "optout".to_string();
    let unset = "unset".to_string();
    let hasdeps = "hasdeps".to_string();
    let sibling = "sibling".to_string();

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(&optin).lib().verify(true),
            MockPackage::new(&optout).lib().verify(false),
            MockPackage::new(&unset).lib(),
            MockPackage::new(&hasdeps)
                .lib()
                .deps([
                    MockDep::workspace(&optin),
                    MockDep::workspace(&optout),
                    MockDep::workspace(&unset),
                ])
                .verify(true),
            MockPackage::new(&sibling).lib().verify(true),
        ])
        .materialize();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&workspace_dir);
        cmd.arg("verify");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--fwd-verus-args-to").arg("all");
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let hasdeps_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_args.contains(&"--verify-module=bar"));

    let optin_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_args.contains(&"--verify-module=bar"));

    let sibling_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn fwd_verus_args_to_roots() {
    let optin = "optin".to_string();
    let optout = "optout".to_string();
    let unset = "unset".to_string();
    let hasdeps = "hasdeps".to_string();
    let sibling = "sibling".to_string();

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(&optin).lib().verify(true),
            MockPackage::new(&optout).lib().verify(false),
            MockPackage::new(&unset).lib(),
            MockPackage::new(&hasdeps)
                .lib()
                .deps([
                    MockDep::workspace(&optin),
                    MockDep::workspace(&optout),
                    MockDep::workspace(&unset),
                ])
                .verify(true),
            MockPackage::new(&sibling).lib().verify(true),
        ])
        .materialize();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&workspace_dir);
        cmd.arg("verify");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--fwd-verus-args-to").arg("roots");
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let hasdeps_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_args.contains(&"--verify-module=bar"));

    let optin_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(!optin_args.contains(&"--verify-module=bar"));

    let sibling_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn fwd_verus_args_to_deps() {
    let optin = "optin".to_string();
    let optout = "optout".to_string();
    let unset = "unset".to_string();
    let hasdeps = "hasdeps".to_string();
    let sibling = "sibling".to_string();

    let workspace_dir = MockWorkspace::new()
        .members([
            MockPackage::new(&optin).lib().verify(true),
            MockPackage::new(&optout).lib().verify(false),
            MockPackage::new(&unset).lib(),
            MockPackage::new(&hasdeps)
                .lib()
                .deps([
                    MockDep::workspace(&optin),
                    MockDep::workspace(&optout),
                    MockDep::workspace(&unset),
                ])
                .verify(true),
            MockPackage::new(&sibling).lib().verify(true),
        ])
        .materialize();
    let workspace_dir = workspace_dir.path().canonicalize().expect("canonical path");

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&workspace_dir);
        cmd.arg("verify");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--fwd-verus-args-to").arg("deps");
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let hasdeps_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(!hasdeps_args.contains(&"--verify-module=bar"));

    let optin_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_args.contains(&"--verify-module=bar"));

    let sibling_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(!sibling_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}
