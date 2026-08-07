mod common;
use common::*;

// run line_count on a file in line_count/test_cases
fn line_count_file(filename: &str) -> String {
    assert!(filename.ends_with(".rs"));
    let file_path = test_cases_path().join(filename);
    run_line_count(&file_path).expect(&format!("line_count failed on {:?}", file_path))
}

#[test]
fn test_line_count_full() {
    insta::assert_snapshot!(line_count_file("full.rs"), @r"
    | file    | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted | Definitions |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | full.rs |       0 |   35 |    15 |   38 |          0 |       7 |      0 | 33          | 1           |
    |---------|---------|------|-------|------|------------|---------|--------|-------------|-------------|
    | total   |       0 |   35 |    15 |   38 |          0 |       7 |      0 | 33          | 1           |
    ");
}

#[test]
fn test_line_count_spec_fn() {
    insta::assert_snapshot!(line_count_file("spec_fn.rs"), @r"
    | file       | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | spec_fn.rs |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    |------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total      |       0 |    7 |     0 | 0    | 0          | 0       | 0      | 6           |
    ");
}

#[test]
fn test_line_count_no_verus() {
    insta::assert_snapshot!(line_count_file("no_verus.rs"), @r"
    | file        | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | no_verus.rs |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    |-------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total       |       0 |    0 | 0     | 0    | 0          | 0       | 0      | 3           |
    ");
}

#[test]
fn test_line_verus_outside() {
    insta::assert_snapshot!(line_count_file("verus_outside.rs"), @r"
    | file             | Trusted | Spec | Proof | Exec | Proof+Exec | Comment | Layout | unaccounted |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | verus_outside.rs |       0 |    3 |     0 | 0    | 0          | 0       | 0      | 15          |
    |------------------|---------|------|-------|------|------------|---------|--------|-------------|
    | total            |       0 |    3 |     0 | 0    | 0          | 0       | 0      | 15          |
    ");
}
