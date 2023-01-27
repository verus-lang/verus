#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

#[test]
fn harness_zero() {
    assert!(
        verify_one_file(code! {
            fn harness1() {
            }
        }, &[])
        .is_ok()
    );
}

#[test]
fn harness_invalid_rust() {
    let code = code! {
        fn harness1() {
            invalid(true);
        }
    };
    let err = verify_one_file(code,  &[]).unwrap_err();
    assert_eq!(err.errors.len(), 0);
}

#[test]
fn harness_true() {
    assert!(
        verify_one_file(code! {
            fn harness1() {
                assert(true);
            }
        }, &[])
        .is_ok()
    );
}

#[test]
fn harness_false() {
    let err = verify_one_file(code! {
        fn harness2() {
            assert(false); // FAILS
        }
    }, &[])
    .unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].first().expect("span").test_span_line.contains("FAILS"));
}

test_verify_one_file! {
    #[test] harness_macro_true code! {
        fn empty() { }

        fn harness1_macro() {
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] harness_macro_false code! {
        fn empty() { }

        fn harness2_macro() {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
