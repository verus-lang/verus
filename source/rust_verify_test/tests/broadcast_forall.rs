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

test_verify_one_file! {
    #[test] test_sm verus_code! {
        // This tests the fix for an issue with the heuristic for pushing broadcast_forall
        // functions to the front.
        // Specifically, the state_machine! macro generates some external_body functions
        // which got pushed to the front by those heurstics. But those external_body functions
        // depended on the the proof fn `stuff_inductive` (via the extra_dependencies mechanism)
        // This caused the `stuff_inductive` to end up BEFORE the broadcast_forall function
        // it needed.

        use vstd::*;
        use state_machines_macros::*;

        pub spec fn f() -> bool;

        #[verifier::external_body]
        #[verifier::broadcast_forall]
        proof fn f_is_true()
            ensures f(),
        {
        }

        state_machine!{ X {
            fields {
                pub a: u8,
            }

            transition!{
                stuff() {
                    update a = 5;
                }
            }

            #[invariant]
            pub spec fn inv(&self) -> bool {
                true
            }

            #[inductive(stuff)]
            fn stuff_inductive(pre: Self, post: Self) {
                assert(f());
            }
        }}
    } => Ok(())
}
