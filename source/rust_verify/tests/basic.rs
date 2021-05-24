#![feature(rustc_private)]

mod common;
use common::*;

#[test]
fn basic_invalid_rust() {
    let code = rust_code! {
        fn basic1() {
            invalid(true);
        }
    };
    let err = rust_verify_with_pervasive(code).unwrap_err();
    assert_eq!(err.len(), 0);
}

#[test]
fn basic_true() {
    let code = rust_code! {
        fn basic1() {
            assert(true);
        }
    };
    let status = rust_verify_with_pervasive(code);
    assert!(status.is_ok());
}

#[test]
fn basic_false() {
    let code = rust_code! {
        fn basic2() {
            assert(false); // FAILS
        }
    };
    let err = rust_verify_with_pervasive(code).unwrap_err();
    assert_eq!(err.len(), 1);
    assert!(err[0].0.as_ref().expect("span").test_span_line.contains("FAILS"));
}
