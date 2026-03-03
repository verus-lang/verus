use std::env;
use std::ffi::OsString;
use std::process;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    println!("cargo:rustc-check-cfg=cfg(exhaustive)");
    println!("cargo:rustc-check-cfg=cfg(prettyplease_debug)");
    println!("cargo:rustc-check-cfg=cfg(prettyplease_debug_indent)");

    let pkg_version = cargo_env_var("CARGO_PKG_VERSION");
    println!("cargo:VERSION={}", pkg_version.to_str().unwrap());

    // See https://github.com/verus-lang/verus/pull/1438
    /*
    let pkg_version_major = cargo_env_var("CARGO_PKG_VERSION_MAJOR");
    let pkg_version_minor = cargo_env_var("CARGO_PKG_VERSION_MINOR");
    let manifest_links = cargo_env_var("CARGO_MANIFEST_LINKS");
    assert!(
        pkg_version_major == "0"
            && manifest_links == *format!("prettyplease0{}", pkg_version_minor.to_str().unwrap())
    );
    */
}

fn cargo_env_var(key: &str) -> OsString {
    env::var_os(key).unwrap_or_else(|| {
        eprintln!("Environment variable ${key} is not set during execution of build script");
        process::exit(1);
    })
}
