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
    } => Err(err) => assert_vir_error_msg(err, "'unsafe' only makes sense on exec-mode functions")
}
