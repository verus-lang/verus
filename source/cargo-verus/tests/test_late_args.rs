#[path = "src/utils.rs"]
mod utils;

use std::process::{Command, Stdio};
use utils::*;

// Tests for late Verus argument detection and -Z flag formatting.
// These tests verify that cargo-verus exits with code 2 when:
// 1. Verus-relevant arguments appear after Verus-irrelevant cargo arguments
// 2. -Z flags are written without a space separator

/// Run cargo-verus expecting it to fail before calling cargo (e.g., due to CLI validation).
/// This doesn't set up the fake cargo data file since cargo won't be invoked.
/// Stderr is suppressed to avoid printing warning messages during test runs.
fn run_cargo_verus_expect_early_failure(setup: impl Fn(&mut Command)) -> std::process::ExitStatus {
    let mut cmd = Command::new(assert_cmd::cargo::cargo_bin!("cargo-verus"));
    setup(&mut cmd);
    cmd.stderr(Stdio::null());
    cmd.status().expect("run cargo-verus and get output")
}

// ============================================================================
// Tests for late Verus-relevant argument detection
// ============================================================================

#[test]
fn late_package_arg_after_release() {
    // --package appearing after --release should be detected as a late argument
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        // --release is a Verus-irrelevant arg that gets forwarded
        cmd.arg("--release");
        // --package comes after, so it will be silently ignored by clap
        cmd.arg("--package=foo");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_features_arg_after_release() {
    // --features appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--features=some-feature");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_all_features_arg_after_release() {
    // --all-features appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--all-features");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_no_default_features_arg_after_release() {
    // --no-default-features appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--no-default-features");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_workspace_arg_after_release() {
    // --workspace appearing after --release should be detected
    let workspace_dir =
        MockWorkspace::new().members([MockPackage::new("foo").lib().verify(true)]).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&workspace_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--workspace");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_frozen_arg_after_release() {
    // --frozen appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--frozen");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_locked_arg_after_release() {
    // --locked appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--locked");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_offline_arg_after_release() {
    // --offline appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--offline");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_target_dir_arg_after_release() {
    // --target-dir appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--target-dir=/tmp/foo");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_config_arg_after_release() {
    // --config appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("--config=build.jobs=1");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn late_z_flag_arg_after_release() {
    // -Z appearing after --release should be detected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--release");
        cmd.arg("-Z");
        cmd.arg("unstable-options");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

// ============================================================================
// Tests for -Z flag without space detection
// ============================================================================

#[test]
fn z_flag_without_space_is_rejected() {
    // -Zsomething (without space) should be detected and rejected
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("-Zunstable-options");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn z_flag_with_space_is_accepted() {
    // -Z something (with space) should work fine
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let (status, _data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("-Z").arg("unstable-options");
    });

    // This should succeed (the CLI parsing should pass)
    assert!(status.success());
}

// ============================================================================
// Tests for correct argument ordering (should succeed)
// ============================================================================

#[test]
fn package_before_release_is_ok() {
    // --package appearing before --release should work fine
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let (status, data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--package=foo");
        cmd.arg("--release");
    });

    assert!(status.success());
    // Verify the args were passed correctly
    assert!(data.args.contains(&"--release".to_string()));
    assert!(data.args.contains(&"--package".to_string()) || data.args.contains(&"-p".to_string()));
}

#[test]
fn features_before_release_is_ok() {
    // --features appearing before --release should work fine
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let (status, _data) = run_cargo_verus(|cmd| {
        cmd.current_dir(&package_dir).arg("verify");
        cmd.arg("--features=default");
        cmd.arg("--release");
    });

    assert!(status.success());
}

// ============================================================================
// Tests for focus subcommand (same checks should apply)
// ============================================================================

#[test]
fn focus_late_package_arg_after_release() {
    // Same check for focus subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("focus");
        cmd.arg("--release");
        cmd.arg("--package=foo");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn focus_z_flag_without_space_is_rejected() {
    // Same check for focus subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("focus");
        cmd.arg("-Zunstable-options");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

// ============================================================================
// Tests for build subcommand (same checks should apply)
// ============================================================================

#[test]
fn build_late_package_arg_after_release() {
    // Same check for build subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("build");
        cmd.arg("--release");
        cmd.arg("--package=foo");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn build_z_flag_without_space_is_rejected() {
    // Same check for build subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("build");
        cmd.arg("-Zunstable-options");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

// ============================================================================
// Tests for check subcommand (same checks should apply)
// ============================================================================

#[test]
fn check_late_package_arg_after_release() {
    // Same check for check subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("check");
        cmd.arg("--release");
        cmd.arg("--package=foo");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}

#[test]
fn check_z_flag_without_space_is_rejected() {
    // Same check for check subcommand
    let package_dir = MockPackage::new("foo").lib().verify(true).materialize();

    let status = run_cargo_verus_expect_early_failure(|cmd| {
        cmd.current_dir(&package_dir).arg("check");
        cmd.arg("-Zunstable-options");
    });

    assert!(!status.success());
    assert_eq!(status.code(), Some(2));
}
