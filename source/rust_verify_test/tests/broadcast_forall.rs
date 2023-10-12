#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
        {
            reveal(f);
        }

        proof fn test1() {
            reveal(p);
            assert(f(10));
        }

        proof fn test2() {
            assert(f(10)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i) // FAILS
        {
        }

        proof fn test1() {
            reveal(p);
            assert(f(10));
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p1(i: int)
            ensures f(i)
        {
            reveal(p2);
        }

        #[verifier::broadcast_forall]
        proof fn p2(i: int)
            ensures f(i) // FAILS
        {
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_cycle_disallowed verus_code! {
        #[verifier::opaque]
        spec fn f(i: int) -> bool { true }

        #[verifier::broadcast_forall]
        proof fn p(i: int)
            ensures f(i)
            decreases i
        {
            reveal(p);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot recursively reveal broadcast_forall")
}
