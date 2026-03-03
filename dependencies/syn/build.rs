#![allow(clippy::uninlined_format_args)]

use std::env;
use std::ffi::OsString;
use std::iter;
use std::process::{self, Command, Stdio};

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    // Note: add "/build.rs" to package.include in Cargo.toml if adding any
    // conditional compilation within the library.

    println!("cargo:rustc-cfg=check_cfg");
    println!("cargo:rustc-check-cfg=cfg(check_cfg)");
    println!("cargo:rustc-check-cfg=cfg(fuzzing)");
    println!("cargo:rustc-check-cfg=cfg(syn_disable_nightly_tests)");
    println!("cargo:rustc-check-cfg=cfg(syn_only)");

    if !unstable() {
        println!("cargo:rustc-cfg=syn_disable_nightly_tests");
    }
}

fn unstable() -> bool {
    let rustc = cargo_env_var("RUSTC");
    let rustc_wrapper = env::var_os("RUSTC_WRAPPER").filter(|wrapper| !wrapper.is_empty());
    let rustc_workspace_wrapper =
        env::var_os("RUSTC_WORKSPACE_WRAPPER").filter(|wrapper| !wrapper.is_empty());
    let mut rustc = rustc_wrapper
        .into_iter()
        .chain(rustc_workspace_wrapper)
        .chain(iter::once(rustc));
    let mut cmd = Command::new(rustc.next().unwrap());
    cmd.args(rustc);

    cmd.stdin(Stdio::null());
    cmd.stdout(Stdio::null());
    cmd.stderr(Stdio::null());
    cmd.arg("-");

    // Find out whether this is a nightly or dev build.
    cmd.env_remove("RUSTC_BOOTSTRAP");
    cmd.arg("-Zcrate-attr=feature(rustc_private)");

    // Pass `-Zunpretty` to terminate earlier without writing out any "emit"
    // files. Use `expanded` to proceed far enough to actually apply crate
    // attrs. With `unpretty=normal` or `--print`, not enough compilation
    // happens to recognize that the feature attribute is unstable.
    cmd.arg("-Zunpretty=expanded");

    // Set #![no_std] to bypass loading libstd.rlib. This is a 7.5% speedup.
    cmd.arg("-Zcrate-attr=no_std");

    cmd.arg("--crate-type=lib");
    cmd.arg("--edition=2021");

    if let Some(target) = env::var_os("TARGET") {
        cmd.arg("--target").arg(target);
    }

    // If Cargo wants to set RUSTFLAGS, use that.
    if let Ok(rustflags) = env::var("CARGO_ENCODED_RUSTFLAGS") {
        if !rustflags.is_empty() {
            for arg in rustflags.split('\x1f') {
                cmd.arg(arg);
            }
        }
    }

    // This rustc invocation should take around 0.03 seconds.
    match cmd.status() {
        Ok(status) => status.success(),
        Err(_) => false,
    }
}

fn cargo_env_var(key: &str) -> OsString {
    env::var_os(key).unwrap_or_else(|| {
        eprintln!(
            "Environment variable ${} is not set during execution of build script",
            key,
        );
        process::exit(1);
    })
}
