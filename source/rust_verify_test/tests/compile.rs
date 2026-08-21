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

/// Writes `verus_block` (the contents of a `verus! { ... }` block) to a fresh temp
/// file, compiles it, runs the resulting binary, and returns its captured stdout.
/// For issue-657-style bugs: a silent-erasure miscompilation only shows up at
/// runtime, so `test_verify_one_file!`'s verify-only check can't catch it.
fn compile_and_run(verus_block: &str) -> String {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let code = format!("{}\n{}\nverus! {{\n{}\n}}\n", FEATURE_PRELUDE, USE_PRELUDE, verus_block);
    std::fs::write(&entry_file, code).expect("write source file");

    let output = run_verus_raw(&["--compile", entry_file.to_str().unwrap()], tempdir.path());
    assert!(output.status.success(), "verus failed:\n{}", String::from_utf8_lossy(&output.stderr));

    let exe_name = if cfg!(target_os = "windows") { "test.exe" } else { "test" };
    let exe_path = tempdir.path().join(exe_name);
    assert!(exe_path.exists(), "expected compiled binary at {:?}", exe_path);

    let run_output =
        std::process::Command::new(&exe_path).output().expect("failed to run compiled binary");
    assert!(run_output.status.success(), "compiled binary did not run successfully");
    String::from_utf8_lossy(&run_output.stdout).into_owned()
}

// https://github.com/verus-lang/verus/issues/657: a real `assert`/`assume` function
// called bare inside external_body must actually run, not get silently erased as a
// ghost assertion. Only observable by running the compiled binary.
#[test]
fn external_body_plain_assert_and_assume_fns_issue657() {
    let stdout = compile_and_run(
        r#"
#[verifier::external_body]
fn assert(cond: bool) {
    if cond {
        println!("assert-fn-true");
    } else {
        println!("assert-fn-false");
    }
}

#[verifier::external_body]
fn assume(cond: bool) {
    if cond {
        println!("assume-fn-true");
    } else {
        println!("assume-fn-false");
    }
}

#[verifier::external_body]
fn call_them(x: u32) {
    assert(x == 0);
    assume(x == 1);
}

#[verifier::external_body]
fn main() {
    call_them(5);
    println!("done");
}
"#,
    );
    assert!(stdout.contains("assert-fn-false"), "stdout:\n{}", stdout);
    assert!(stdout.contains("assume-fn-false"), "stdout:\n{}", stdout);
    assert!(stdout.contains("done"), "stdout:\n{}", stdout);
}

// Same as above, for reveal/hide/reveal_with_fuel.
#[test]
fn external_body_plain_reveal_hide_fns_issue657() {
    let stdout = compile_and_run(
        r#"
#[verifier::external_body]
fn reveal(x: bool) {
    println!("reveal-fn:{}", x);
}

#[verifier::external_body]
fn hide(x: bool) {
    println!("hide-fn:{}", x);
}

#[verifier::external_body]
fn reveal_with_fuel(x: bool, n: u32) {
    println!("reveal_with_fuel-fn:{}:{}", x, n);
}

#[verifier::external_body]
fn call_them(flag: bool, fuel: u32) {
    reveal(flag);
    hide(flag);
    reveal_with_fuel(flag, fuel);
}

#[verifier::external_body]
fn main() {
    call_them(true, 7);
    println!("done");
}
"#,
    );
    assert!(stdout.contains("reveal-fn:true"), "stdout:\n{}", stdout);
    assert!(stdout.contains("hide-fn:true"), "stdout:\n{}", stdout);
    assert!(stdout.contains("reveal_with_fuel-fn:true:7"), "stdout:\n{}", stdout);
    assert!(stdout.contains("done"), "stdout:\n{}", stdout);
}
