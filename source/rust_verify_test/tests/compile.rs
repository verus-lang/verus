#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

#[test]
fn compile_flag_produces_binary() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let code = format!("{}\n{}\nverus! {{ fn main() {{}} }}\n", FEATURE_PRELUDE, USE_PRELUDE);
    std::fs::write(&entry_file, code).expect("write source file");

    let output = run_verus_raw(&["--compile", entry_file.to_str().unwrap()], tempdir.path());
    let exe_name = if cfg!(target_os = "windows") { "test.exe" } else { "test" };
    assert!(output.status.success(), "verus failed:\n{}", String::from_utf8_lossy(&output.stderr));
    assert!(tempdir.path().join(exe_name).exists());
}

#[test]
fn no_compile_flag_does_not_produce_binary() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let code = format!("{}\n{}\nverus! {{ fn main() {{}} }}\n", FEATURE_PRELUDE, USE_PRELUDE);
    std::fs::write(&entry_file, code).expect("write source file");

    let output = run_verus_raw(&[entry_file.to_str().unwrap()], tempdir.path());
    let exe_name = if cfg!(target_os = "windows") { "test.exe" } else { "test" };
    assert!(output.status.success(), "verus failed:\n{}", String::from_utf8_lossy(&output.stderr));
    assert!(!tempdir.path().join(exe_name).exists());
}
