use std::process::Command;

use cargo_verus_toolchains::versions::{get_verus_version, git_head_paths};

fn main() {
    let (default_version, default_sha) = get_verus_version(true).expect("version info");
    let profile = std::env::var("VARGO_BUILD_PROFILE")
        .unwrap_or_else(|_| std::env::var("PROFILE").expect("build profile"));
    let version = std::env::var("VARGO_BUILD_VERSION").unwrap_or(default_version);
    let sha = std::env::var("VARGO_BUILD_SHA").unwrap_or(default_sha);
    let toolchain = std::env::var("VARGO_TOOLCHAIN").unwrap_or_else(|_| {
        run_command(&["rustup", "show", "active-toolchain"]).expect("active toolchain")
    });

    for path in git_head_paths().expect("Git HEAD paths") {
        println!("cargo::rerun-if-changed={}", path.display());
    }
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_PROFILE");
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_VERSION");
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_SHA");
    println!("cargo::rerun-if-env-changed=VARGO_TOOLCHAIN");

    println!("cargo::rustc-env=VARGO_BUILD_PROFILE={profile}");
    println!("cargo::rustc-env=VARGO_BUILD_VERSION={version}");
    println!("cargo::rustc-env=VARGO_BUILD_SHA={sha}");
    println!("cargo::rustc-env=VARGO_TOOLCHAIN={toolchain}");
}

fn run_command(program_and_args: &[&str]) -> Option<String> {
    let output = Command::new(program_and_args[0]).args(&program_and_args[1..]).output().ok()?;
    output.status.success().then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}
