#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] unsafe_fns_ok verus_code! {
        unsafe fn f() {
        }

        #[verifier::external]
        unsafe fn g() {
        }

        #[verifier::external_body]
        unsafe fn h() {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unsafe_proof_fn_fail verus_code! {
        unsafe proof fn j() {
        }
    } => Err(err) => assert_vir_error_msg(err, "`unsafe` only makes sense on exec-mode functions")
}

test_verify_one_file! {
    #[test] unsafe_attr verus_code! {
        #[no_mangle]
        pub extern "C" fn malloc(size: usize) -> usize {
            4096
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support the `no_mangle` attribute, which is unsafe")
}
