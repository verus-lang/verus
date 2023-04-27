#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

#[test]
fn harness_zero() {
    assert!(
        verify_one_file(
            "harness_zero",
            verus_code! {
                fn harness1() {
                }
            },
            &[]
        )
        .is_ok()
    );
}

#[test]
fn harness_invalid_rust() {
    let code = verus_code! {
        fn harness1() {
            invalid(true);
        }
    };
    let err = verify_one_file("harness_invalid_rust", code, &[]).unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert_rust_error_msg(err, "cannot find function `invalid` in this scope");
}

#[test]
fn harness_true() {
    assert!(
        verify_one_file(
            "harness_true",
            verus_code! {
                fn harness1() {
                    assert(true);
                }
            },
            &[]
        )
        .is_ok()
    );
}

#[test]
fn harness_false() {
    let err = verify_one_file(
        "harness_false",
        verus_code! {
            fn harness2() {
                assert(false); // FAILS
            }
        },
        &[],
    )
    .unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert!(err.errors[0].spans.first().expect("span").text[0].text.contains("FAILS"));
}

test_verify_one_file! {
    #[test] harness_macro_true verus_code! {
        fn empty() { }

        fn harness1_macro() {
            assert(true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] harness_macro_false verus_code! {
        fn empty() { }

        fn harness2_macro() {
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
