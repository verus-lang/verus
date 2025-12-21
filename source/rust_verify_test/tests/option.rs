#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_unwrap_expect verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        proof fn test_option() {
            let ok_option = Option::<i8>::Some(1);
            assert(ok_option is Some);
            assert(ok_option.unwrap() == 1);
            let ok_option2 = Option::<i8>::Some(1);
            assert(ok_option2 is Some);
            assert(ok_option2.expect("option was built with Some") == 1);
            let none_option = Option::<i8>::None;
            assert(none_option is None);
        }
    } => Ok(())
}
