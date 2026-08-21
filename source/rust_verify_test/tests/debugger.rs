#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

// The debugger shell resolves a reassigned variable to its concrete, correct value at
// each point - not a stale (pre-reassignment) value, and not a live Z3 round-trip that
// can fail with `(error "model is not available")`. (The plain "doesn't panic on
// reassignment under -V debug" case is covered more simply in regression.rs.)
#[test]
fn debugger_shell_reports_correct_value_across_a_reassignment() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");

    // Don't hand-count FEATURE_PRELUDE/USE_PRELUDE's line count (fragile, and not our
    // concern here) - compute the real offset so the `verus! { ... }` block's own line
    // numbers below are accurate regardless of how long the prelude actually is.
    let prelude = format!("{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE);
    let prelude_lines = prelude.lines().count();
    let body =
        "verus! {\nfn f() {\nlet mut x: u32 = 5;\nx = 10;\nassert(x == 999);\n}\n}\nfn main() {}\n";
    // Line (1-indexed) of `let mut x: u32 = 5;` and `x = 10;` within `body`.
    let reassign_decl_line = prelude_lines + 3;
    let reassign_stmt_line = prelude_lines + 4;
    std::fs::write(&entry_file, format!("{}{}", prelude, body)).expect("write source file");

    let output = run_verus_raw_with_stdin(
        &["-V", "debug", "--num-threads", "1", entry_file.to_str().unwrap()],
        tempdir.path(),
        &format!("line {}\nx\nline {}\nx\nquit\n", reassign_decl_line, reassign_stmt_line),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("model is not available"), "stdout:\n{}", stdout);

    // The prompt (`print!`, no trailing newline) and the evaluated value (`println!`)
    // land on the same physical line, e.g. "verus-debug> 5" - so look for the value as
    // the tail end of a "verus-debug> " line, not a bare line on its own.
    let lines: Vec<&str> = stdout
        .lines()
        .filter_map(|l| l.trim().strip_prefix("verus-debug>").map(|v| v.trim()))
        .collect();
    let before = lines.iter().position(|l| *l == "5").expect("value before reassignment");
    let after = lines.iter().position(|l| *l == "10").expect("value after reassignment");
    assert!(
        before < after,
        "expected the pre-reassignment value (5) before the post-reassignment value (10):\n{}",
        stdout
    );
}

// A function application like `(add_one x)` used to either hit a live Z3 round-trip
// that reliably fails with "model is not available", or a naive AIR name (missing the
// crate prefix) that fails with "unknown constant". Both are fixed by evaluating
// straight from the captured model instead.
#[test]
fn debugger_shell_evaluates_a_function_application_from_the_model() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");

    let prelude = format!("{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE);
    let body = "verus! {\nspec fn add_one(x: int) -> int { x + 1 }\nfn f() {\nlet x: u32 = 5;\nassert(add_one(x as int) == 999);\n}\n}\nfn main() {}\n";
    let assert_line = prelude.lines().count() + 4;
    std::fs::write(&entry_file, format!("{}{}", prelude, body)).expect("write source file");

    let output = run_verus_raw_with_stdin(
        &["-V", "debug", "--num-threads", "1", entry_file.to_str().unwrap()],
        tempdir.path(),
        &format!("line {}\n(add_one x)\nquit\n", assert_line),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("model is not available"), "stdout:\n{}", stdout);
    assert!(!stdout.contains("unknown constant"), "stdout:\n{}", stdout);

    let lines: Vec<&str> = stdout
        .lines()
        .filter_map(|l| l.trim().strip_prefix("verus-debug>").map(|v| v.trim()))
        .collect();
    assert!(lines.iter().any(|l| *l == "6"), "expected '6' among evaluated values:\n{}", stdout);
}
