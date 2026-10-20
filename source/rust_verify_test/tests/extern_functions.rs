#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] extern_function_basic verus_code! {
        extern "C" {
            #[verifier::external_body]
            fn foo(x: u8) -> u8;
        }

        fn test() {
            let y = foo(0);
            assert(0 <= y < 256);
        }

        fn test2() {
            let y = foo(0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] extern_function_must_be_external_body verus_code! {
        extern "C" {
            fn foo(x: u8) -> u8;
        }
    } => Err(err) => assert_vir_error_msg(err, "extern function cannot be checked")
}
