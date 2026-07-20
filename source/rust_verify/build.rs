use std::process::Command;

fn main() {
    let (default_version, default_sha) = get_version_info().expect("version info");
    let profile = std::env::var("VARGO_BUILD_PROFILE")
        .unwrap_or_else(|_| std::env::var("PROFILE").expect("build profile"));
    let version = std::env::var("VARGO_BUILD_VERSION").unwrap_or(default_version);
    let sha = std::env::var("VARGO_BUILD_SHA").unwrap_or(default_sha);
    let toolchain = std::env::var("VARGO_TOOLCHAIN").unwrap_or_else(|_| {
        run_command(&["rustup", "show", "active-toolchain"]).expect("active toolchain")
    });

    println!("cargo::rerun-if-changed=../.git/HEAD");
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_PROFILE");
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_VERSION");
    println!("cargo::rerun-if-env-changed=VARGO_BUILD_SHA");
    println!("cargo::rerun-if-env-changed=VARGO_TOOLCHAIN");

    println!("cargo::rustc-env=VARGO_BUILD_PROFILE={profile}");
    println!("cargo::rustc-env=VARGO_BUILD_VERSION={version}");
    println!("cargo::rustc-env=VARGO_BUILD_SHA={sha}");
    println!("cargo::rustc-env=VARGO_TOOLCHAIN={toolchain}");
}

fn get_version_info() -> Option<(String, String)> {
    let short_sha = run_command(&["git", "rev-parse", "--short=7", "HEAD"])?;
    let sha = run_command(&["git", "rev-parse", "HEAD"])?;
    let date = run_command(&["git", "show", "-s", "--format=%cs", "HEAD"])?;
    let mut date = date.split('-');
    let (Some(year), Some(month), Some(day), None) =
        (date.next(), date.next(), date.next(), date.next())
    else {
        return None;
    };
    let dirty = run_command(&["git", "diff", "--exit-code", "HEAD"]).is_none();
    let dirty_suffix = if dirty { ".dirty" } else { "" };
    Some((format!("0.{year}.{month}.{day}.{short_sha}{dirty_suffix}"), sha))
}

fn run_command(program_and_args: &[&str]) -> Option<String> {
    let output = Command::new(program_and_args[0]).args(&program_and_args[1..]).output().ok()?;
    output.status.success().then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}
