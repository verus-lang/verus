#![allow(unused)]

use std::ffi::OsStr;
use std::io::Error;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Finds the path for the line_count binary
///
/// Should correctly find it for both `cargo test` and `cargo nextest`, and
/// find the correct build (release/debug)
pub fn line_count_path() -> PathBuf {
    let bin_name_str = std::env::var("CARGO_BIN_EXE_line_count")
        .or(std::env::var("NEXTEST_BIN_EXE_line_count"))
        .unwrap();

    Path::new(&bin_name_str).to_owned()
}

/// Finds the path to `vstd`, based on relative location to `line_count`'s Cargo.toml
pub fn vstd_path() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    Path::new(&manifest_dir).join("../../vstd")
}

/// Finds the path to `examples`, based on relative location to `line_count`'s Cargo.toml
pub fn examples_path() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    Path::new(&manifest_dir).join("../../../examples")
}

/// Finds the path to `test_cases`, based on relative location to `line_count`'s Cargo.toml
pub fn test_cases_path() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    Path::new(&manifest_dir).join("./test_cases")
}

/// Run line_count on a particular path
/// Returns the String of the output
///
/// Returns Err if the command could not be run, or if it exited unsuccessfully
pub fn run_line_count<P: AsRef<Path>>(path: P) -> Result<String, std::io::Error> {
    let (stdout, _stderr) = run_line_count_with_args(path, &[])?;
    Ok(stdout)
}

/// Run line_count on a particular path, passing additional command-line arguments
/// Returns the Strings of the (stdout, stderr) output
///
/// Returns Err if the command could not be run, or if it exited unsuccessfully
pub fn run_line_count_with_args<P: AsRef<Path>>(
    path: P,
    args: &[&str],
) -> Result<(String, String), std::io::Error> {
    let line_count_path = &line_count_path();

    let path = path.as_ref();

    let mut cmd = Command::new(line_count_path);
    cmd.args(args);
    cmd.arg(path);
    eprintln!("cmd: {cmd:?}");
    let output = cmd.output()?;
    let stdout = String::from_utf8(output.stdout).expect("line count returned non-utf8");
    let stderr = String::from_utf8(output.stderr).expect("line count returned non-utf8");
    // `output()` only fails if the command could not be run, so check the exit status as well
    if !output.status.success() {
        return Err(Error::other(format!(
            "line_count exited with {}\nstderr:\n{stderr}",
            output.status
        )));
    }
    Ok((stdout, stderr))
}
