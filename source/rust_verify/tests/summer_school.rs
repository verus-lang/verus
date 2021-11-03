#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// -- e01 --

test_verify_with_pervasive! {
    #[test] e01_pass code! {
        fn e01(p: int) {
            assert(5 > 3);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e01_fail code! {
        fn e01(p: int) {
            assert(5 < 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e02 --

test_verify_with_pervasive! {
    #[test] e02_pass code! {
        fn e02(p: int) {
            assert(imply(true, true));
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e02_fail code! {
        fn e02(p: int) {
            assert(imply(true, false)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// -- e03 --

const E03_SHARED: &str = code_str! {
    #[spec]
    fn double(val: int) -> int {
        2 * val
    }
};

test_verify_with_pervasive! {
    #[test] e03_pass E03_SHARED.to_string() + code_str! {
        #[proof]
        fn double_is_like_plus(p: int) {
            assert(double(6) == 6 + 6);
            assert(double(-2) == -4);
        }

        #[proof]
        fn foo4(val: int) {
            assert(double(val) == val + val);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] e03_fail E03_SHARED.to_string() + code_str! {
        #[proof]
        fn double_is_like_plus(p: int) {
            assert(double(-2) == 4); // FAILS
        }

        #[proof]
        fn foo4(val: int) {
            assert(double(val) == val + val + val); // FAILS
        }
    } => Err(err) => assert_two_fails(err)
}
