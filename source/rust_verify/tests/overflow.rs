#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_overflow_pass code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2;
            assert(j == a + 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_overflow_fails_1 code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2;
            assert(j == a as nat + 2); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_overflow_fails_2 code! {
        fn test(a: u64) {
            let mut j = a;
            j = j + 2;
            j = j + 2;
            assert(j == a + 4); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
