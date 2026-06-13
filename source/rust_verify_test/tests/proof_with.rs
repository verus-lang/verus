#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
     #[test] test_proof_with verus_code!{
        use vstd::prelude::*;
        fn test(a: u64)
        {
            let b: Tracked<u64> = declare_with();
            let c: Ghost<u32> = declare_with();
            requires(a == 0 && b@ == 1 && c@ == 2);
        }

        fn call_test() {
            proof_with((Tracked(1u64), Ghost(2u32)), test(0));
        }

        #[verifier(external)]
        fn unverified_call_test() {
            test(0);
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_impl verus_code!{
        use vstd::prelude::*;
        struct A {
            a: u64
        }
        impl A {
            fn test(&self)
            {
                let b: Tracked<u64> = declare_with();
                let c: Ghost<u32> = declare_with();
                requires(self.a == 0 && b@ == 1 && c@ == 2);
            }
        }
        fn call_test() {
            let a = A { a: 0 };
            proof_with((Tracked(1u64), Ghost(2u32)), a.test());
        }

        #[verifier(external)]
        fn unverified_call_test() {
            let a = A { a: 0 };
            a.test();
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_trait verus_code!{
        use vstd::prelude::*;
        struct A {
            a: u64
        }

        trait AOp {
            fn test(&self) {
                let b: Tracked<u64> = declare_with();
                let c: Ghost<u32> = declare_with();
                requires(b@ == 1 && c@ == 2);
            }
        }
        impl AOp for A {
            fn test(&self)
            {
                let b: Tracked<u64> = declare_with();
                let c: Ghost<u32> = declare_with();
                assert(b@ == 1);
                assert(c@ == 0); // FAILS
            }
        }
        fn call_test() {
            let a = A { a: 0 };
            proof_with((Tracked(1u64), Ghost(2u32)), a.test());
        }

        #[verifier(external)]
        fn unverified_call_test() {
            let a = A { a: 0 };
            a.test();
        }
     } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
     #[test] test_proof_with_external verus_code!{
        use vstd::prelude::*;
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            let extra: Tracked<u8> = declare_with();
            requires(x == extra@);
            ensures(|ret_b: bool| ret_b == !b);
            negate_bool(b, x)
        }

        fn call_test() {
            proof_with(Tracked(1u8), negate_bool(true, 1));
        }

        #[verifier(external)]
        fn unverified_call_test() {
            negate_bool(true, 1);
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_external_failed verus_code!{
        use vstd::prelude::*;
        #[verifier(external)]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool
        {
            let extra: Tracked<u8> = declare_with();
            requires(x == extra@);
            ensures(|ret_b: bool| ret_b == !b);
            negate_bool(b, x)
        }

        fn call_test() {
            negate_bool(true, 1);
        }
     } => Err(e) => assert_vir_error_msg(e, "this function requires 1 extra tracked/ghost argument(s) via proof_with()")
}

test_verify_one_file! {
     #[test] test_proof_with_failed_requires verus_code!{
        use vstd::prelude::*;
        fn test(a: u64)
        {
            let b: Tracked<u64> = declare_with();
            let c: Ghost<u32> = declare_with();
            requires(a == 0 && b@ == 1 && c@ == 2);
        }

        fn call_test() {
            proof_with((Tracked(0u64), Ghost(2u32)), test(0)); // FAILS
        }
     } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
     #[test] test_proof_with_invalid_type verus_code!{
        use vstd::prelude::*;
        fn test(a: u64)
        {
            let b: Tracked<u64> = declare_with();
            requires(a == 0 && b@ == 1);
        }

        fn call_test() {
            proof_with(0u64, test(0));
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with expects arguments of type Tracked<T> or Ghost<T>")
}

test_verify_one_file! {
     #[test] test_proof_with_wrong_mode_type verus_code!{
        use vstd::prelude::*;
        fn test(a: u64)
        {
            let b: Tracked<u64> = declare_with();
            requires(a == 0 && b@ == 1);
        }

        fn call_test() {
            proof_with(Ghost(0u64), test(0));
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with argument 1 has wrong mode: expected Tracked, got Ghost")
}

// ---- Lifetime soundness tests ----
// These tests verify that lifetime constraints on tracked/ghost params are properly checked.

test_verify_one_file! {
    #[test] test_proof_with_lifetime_mismatch verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64, b: u64) -> u64
        {
            let c: Tracked<&'a u64> = declare_with();
            1
        }

        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64
        {
            proof_with(c, test(a, b))
        }
    } => Err(err) => assert_vir_error_msg(err, "proof_with argument 1 has incompatible lifetime")
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_compatible verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64, b: u64) -> u64
        {
            let c: Tracked<&'a u64> = declare_with();
            1
        }

        fn test2<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64
        {
            proof_with(c, test(a, b))
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_bound_mismatch verus_code!{
        use vstd::prelude::*;
        fn test<'a, 'b: 'a>(a: &'a u64, b: u64) -> &'a u64
        {
            let c: Tracked<&'b u64> = declare_with();
            a
        }

        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> &'a u64
        {
            proof_with(c, test(a, b))
        }
    } => Err(err) => assert_vir_error_msg(err, "proof_with argument 1 has incompatible lifetime")
}

// Same as test_proof_with_lifetime_mismatch but for Ghost.
test_verify_one_file! {
    #[test] test_declare_with_ghost_lifetime_mismatch verus_code!{
        use vstd::prelude::*;
        fn test<'a>(a: &'a u64) -> u64
        {
            let g: Ghost<&'a u64> = declare_with();
            1
        }

        fn test2<'a, 'b>(a: &'a u64, c: Ghost<&'b u64>) -> u64
        {
            proof_with(c, test(a))
        }
    } => Err(err) => assert_vir_error_msg(err, "proof_with argument 1 has incompatible lifetime")
}

test_verify_one_file! {
     #[test] test_proof_with_generic_type verus_code!{
        use vstd::prelude::*;
        fn test<T>(a: T)
        {
            let b: Tracked<T> = declare_with();
            let c: Ghost<u32> = declare_with();
            requires(a === b@ && c@ == 2);
        }

        fn call_test() {
            proof_with((Tracked(0u64), Ghost(2u32)), test(0u64));
        }

        #[verifier(external)]
        fn unverified_call_test() {
            test(0u64);
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_generic_type2 verus_code!{
        use vstd::prelude::*;
        trait X {}
        fn test<T1: X, T2>(a: T1, b: T2)
        {
            let c: Tracked<T2> = declare_with();
            let d: Ghost<u32> = declare_with();
        }

        fn call_test<T1: X, T2>(a: T1, b: T2, c: Tracked<T2>, d: Ghost<u32>) {
            proof_with((c, d), test(a, b));
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_generic_type_wrong_type verus_code!{
        use vstd::prelude::*;
        fn test<T>(a: T)
        {
            let b: Tracked<T> = declare_with();
            let c: Ghost<u32> = declare_with();
            requires(a === b@ && c@ == 2);
        }

        fn call_test() {
            proof_with((Tracked(0u8), Ghost(2u32)), test(0u64));
        }

        #[verifier(external)]
        fn unverified_call_test() {
            test(0u64);
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with argument 1 has wrong type")
}

test_verify_one_file! {
     #[test] test_proof_with_ownership verus_code!{
        use vstd::prelude::*;

        struct A;

        fn test<'a>(a: &'a mut A)
        {
            let b: Tracked<&'a mut A> = declare_with();
            let c: Ghost<u32> = declare_with();
        }

        fn call_test(mut a: A, mut b: A) {
            proof_with((Tracked(&mut a), Ghost(2u32)), test(&mut a));
        }
     } => Err(e) => assert_rust_error_msg_skip_spec_msgs(e, "cannot borrow `a` as mutable more than once at a time")
}

// ---- declare_ret_with / proof_with_ret tests ----

test_verify_one_file! {
     #[test] test_declare_ret_with_basic verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let mut out1: Tracked<u8> = declare_ret_with();
            proof {
                out1 = Tracked(42u8);
            }
            1
        }

        fn call_test() {
            let (ret, extra): (_, (Tracked<u8>,)) = proof_with_ret((), callee(5));
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_declare_ret_with_no_assigned verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let mut out1: Tracked<u8> = declare_ret_with();
            1
        }

        fn call_test() {
            let (ret, extra): (_, (Tracked<u8>,)) = proof_with_ret((), callee(5));
        }
     } => Err(e) => assert_any_vir_error_msg(e, "declare_ret_with() variable must be assigned to")
}

test_verify_one_file! {
     #[test] test_declare_ret_with_multiple verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let mut out1: Tracked<u8> = declare_ret_with();
            let mut out2: Ghost<u32> = declare_ret_with();
            
            proof { 
                out1 = Tracked(42u8);
                out2 = Ghost(7u32);
            }
            1
        }

        fn call_test() {
            let (ret, (e1, e2)): (_, (Tracked<u8>, Ghost<u32>)) = proof_with_ret((), callee(5));
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_declare_ret_with_with_inputs verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let inp: Tracked<u64> = declare_with();
            let mut out1: Tracked<u8> = declare_ret_with();
            proof { out1 = Tracked(0u8); }
            1
        }

        fn call_test() {
            let (ret, extra): (_, (Tracked<u8>,)) = proof_with_ret(Tracked(42u64), callee(5));
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_declare_ret_with_outside_let verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            declare_ret_with::<Tracked<u8>>();
            1
        }
     } => Err(e) => assert_vir_error_msg(e, "declare_ret_with() must be used as a let initializer")
}

test_verify_one_file! {
     #[test] test_declare_ret_with_requires_mut verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let out1: Tracked<u8> = declare_ret_with();
            1
        }
     } => Err(e) => assert_vir_error_msg(e, "declare_ret_with() variable must be declared as `let mut`")
}

test_verify_one_file! {
     #[test] test_declare_ret_with_ensures verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let mut out1: Tracked<u8> = declare_ret_with();
            ensures(|ret: u64| ret == 1 && out1@ == 42);

            proof { out1 = Tracked(42u8); }
            1
        }

        fn call_test() {
            let tracked z2: u8;
            let (_ret, (tmp_z2,)): (_, (Tracked<u8>,)) = proof_with_ret((), callee(5));
            proof {
                z2 = tmp_z2.get();
            }

        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_declare_ret_with_ensures_fail verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
            let mut out1: Tracked<u8> = declare_ret_with();
            ensures(|ret: u64| ret == 1 && out1@ == 42);

            proof { out1 = Tracked(10u8); } // FAILS
            1
        }
     } => Err(e) => assert!(e.errors.len() > 0)
}

// Tests for ensures propagation when both declare_with and declare_ret_with are present.
// This verifies that the caller can assert postconditions about both:
// - The tracked/ghost input params (old/final semantics)
// - The extra return values from declare_ret_with

test_verify_one_file! {
     #[test] test_declare_ret_with_caller_assert verus_code!{
        use vstd::prelude::*;
        fn callee(a: u64) -> u64
        {
           let mut out1: Tracked<u8> = declare_ret_with();
           ensures(|ret: u64| ret == 1 && out1@ == 42);

           proof { out1 = Tracked(42u8); }
           1
        }

        fn call_test() {
           let tracked z2: u8;
           let (_ret, (tmp_z2,)): (_, (Tracked<u8>,)) = proof_with_ret((), callee(5));
           proof {
               z2 = tmp_z2.get();
               assert(z2 == 42);
           }
           assert(_ret == 1);
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_declare_with_and_ret_with_ensures verus_code!{
        use vstd::prelude::*;

        // Function with both declare_with (input) and declare_ret_with (output)
        fn callee(x: u32) -> u32
        {
           let w: Ghost<u32> = declare_with();
           let mut z: Ghost<u32> = declare_ret_with();
           requires(w@ < 100);
           ensures(|ret: u32| ret == x && z@ == x);

           proof {
               z = Ghost(x);
           }
           x
        }

        fn caller_test() {
           let ghost z: u32;
           let (_ret, (tmp_z,)): (_, (Ghost<u32>,)) = proof_with_ret(
               (Ghost(0u32),),
               callee(1)
           );
           proof {
               z = tmp_z.view();
               assert(z == 1);   // from z@ == x postcondition
           }
           assert(_ret == 1);    // from ret == x postcondition
        }
     } => Ok(())
}

test_verify_one_file! {
     #[test] test_proof_with_tracked_mut_ensures verus_code!{
        use vstd::prelude::*;

        // Function with only declare_with (tracked value), no declare_ret_with
        fn set_val(x: u32) -> u32
        {
           let y: Tracked<u64> = declare_with();
           requires((x as u64) < 100 && y@ < 100);
           ensures(|ret: u32| ret == x);

           x
        }

        fn caller_test() {
           let ret = proof_with((Tracked(1u64),), set_val(1));
           assert(ret == 1);

           let ret2 = proof_with((Tracked(42u64),), set_val(42));
           assert(ret2 == 42);
        }
     } => Ok(())
}
