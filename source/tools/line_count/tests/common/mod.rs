#![allow(unused)]

use std::ffi::OsStr;
use std::process::Command;

/// Finds the path for the line_count binary
///
/// Should correctly find it for both `cargo test` and `cargo nextest`, and
/// find the correct build (release/debug)
pub fn line_count_path() -> std::path::PathBuf {
    let bin_name_str = std::env::var("CARGO_BIN_EXE_line_count")
        .or(std::env::var("NEXTEST_BIN_EXE_line_count"))
        .unwrap();

    std::path::Path::new(&bin_name_str).to_owned()
}

/// Finds the path to `vstd`, based on relative location to `line_count`'s Cargo.toml
pub fn vstd_path() -> std::path::PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    std::path::Path::new(&manifest_dir).join("../../vstd")
}

/// Finds the path to `examples`, based on relative location to `line_count`'s Cargo.toml
pub fn examples_path() -> std::path::PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    std::path::Path::new(&manifest_dir).join("../../vstd")
}

/// Finds the path to `test_cases`, based on relative location to `line_count`'s Cargo.toml
pub fn test_cases_path() -> std::path::PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    std::path::Path::new(&manifest_dir).join("./test_cases")
}

/// Run line_count on a particular path
/// Returns the String of the output
///
/// Only returns Err if the command itself failed
pub fn run_line_count<P: AsRef<std::path::Path>>(path: P) -> Result<String, std::io::Error> {
    let line_count_path = &line_count_path();

    let path = path.as_ref();

    let mut cmd = Command::new(line_count_path);
    cmd.arg("--one-file");
    cmd.arg(path);
    let output = cmd.output()?;
    Ok(String::from_utf8(output.stdout).expect("line count returned non-utf8"))
}
