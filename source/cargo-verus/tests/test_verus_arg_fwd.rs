#[path = "src/utils.rs"]
mod utils;

use utils::*;

#[test]
fn workspace_explicit_all() {
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

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_explicit_roots() {
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

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(!optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_explicit_deps() {
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

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(!hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(!sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_verify_is_all() {
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
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_build_is_all() {
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
        cmd.arg("build");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_check_is_all() {
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
        cmd.arg("check");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}

#[test]
fn workspace_default_for_focus_is_roots() {
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
        cmd.arg("focus");
        cmd.arg("--package").arg(&hasdeps);
        cmd.arg("--package").arg(&sibling);
        cmd.arg("--");
        cmd.arg("--verify-module=bar");
    });

    assert!(status.success());

    let driver_args = data.parse_driver_args(" __VERUS_DRIVER_ARGS__");
    assert!(
        !driver_args.contains(&"--verify-module=bar"),
        "forwarded Verus args should not be in __VERUS_DRIVER_ARGS__"
    );

    let hasdeps_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{hasdeps}-0.1.0-"));
    assert!(hasdeps_driver_args.contains(&"--verify-module=bar"));

    let optin_driver_args =
        data.parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optin}-0.1.0-"));
    assert!(!optin_driver_args.contains(&"--verify-module=bar"));

    let sibling_driver_args = data
        .parse_driver_args_for_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{sibling}-0.1.0-"));
    assert!(sibling_driver_args.contains(&"--verify-module=bar"));

    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{optout}-0.1.0-"));
    data.assert_env_has_no_key_prefix(&format!(" __VERUS_DRIVER_ARGS_FOR_{unset}-0.1.0-"));
}
