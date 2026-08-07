mod common;
use common::*;

// Test that all files in vstd are parseable with line_count
#[test]
fn line_count_vstd() {
    test_line_count_does_not_error(vstd_path());
}

// Test that all files in examples are parseable with line_count
#[test]
fn line_count_examples() {
    test_line_count_does_not_error(examples_path());
}

// Test that all files in a dir are parseable with line_count
fn test_line_count_does_not_error<P: AsRef<std::path::Path>>(dir: P) {
    let dir = dir.as_ref();
    run_line_count(dir).expect(&format!("line_count shouldn't fail on {:?}", dir));
}
