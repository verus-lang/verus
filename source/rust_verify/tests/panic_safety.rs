#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    // TODO SOUNDNESS this code verifies, but panics in debug mode
    // introduce under/overflow checks
    #[ignore] #[test] verified_code_should_not_panic code! {
        fn do_not_panic() {
            let mut a: u64 = 0;
            a = a - 1; // TODO this should produce an error
        }
    } => Err(_)
}
