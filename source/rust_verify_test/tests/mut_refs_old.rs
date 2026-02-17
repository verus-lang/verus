#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_old_spec_fn ["new-mut-ref"] => verus_code! {
        spec fn foo(x: &mut u64) -> u64 {
            *old(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless in spec functions")
}

test_verify_one_file_with_options! {
    #[test] test_old_spec_fn_sig ["new-mut-ref"] => verus_code! {
        spec fn foo(x: &mut u64) -> u64
            recommends *old(x) == 0
        {
            0
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless in spec functions")
}
