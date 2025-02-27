#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] recursive_exec_function_needs_decreases_clause verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures r == i
        {
            if i == 0 {
                return 0;
            } else {
                return 1 + a(i - 1);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file_with_options! {
    #[test] nontermination_allowed_with_attribute ["may_not_terminate"] => verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures false
        {
            loop {}
        }
    } => Ok(())
}
