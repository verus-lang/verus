#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] ensures_forall_recommends_failure verus_code! {
        spec fn foo(i: int) -> bool
          recommends 0 <= i < 5,
        {
          i + 3 == 20
        }

        proof fn some_proof()
            ensures forall |i: int| 0 <= i < 20 ==> foo(i),  // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}
