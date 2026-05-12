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
            proof_with(Tracked(1u64));
            proof_with(Ghost(2u32));
            test(0);
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
            proof_with(Tracked(1u64));
            proof_with(Ghost(2u32));
            a.test();
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
            proof_with(Tracked(1u64));
            proof_with(Ghost(2u32));
            a.test();
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
            proof_with(Tracked(1u8));
            negate_bool(true, 1);
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
     } => Err(e) => assert_vir_error_msg(e, "this external function requires 1 extra tracked/ghost argument(s) via proof_with()")
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
            proof_with(Tracked(0u64));
            proof_with(Ghost(2u32));
            test(0); // FAILS
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
            proof_with(0u64);
            test(0);
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with expects an argument of type Tracked<T> or Ghost<T>")
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
            proof_with(Ghost(0u64));
            test(0);
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with argument 1 has wrong mode: expected Tracked, got Ghost")
}

// ---- Lifetime soundness tests ----
// These tests verify that lifetime constraints on tracked/ghost params are properly checked.

// BUG: This should fail with a lifetime error but currently passes.
// The tracked param Tracked<&'b u64> is passed where Tracked<&'a u64> is expected,
// but 'b may not outlive 'a. This is unsound.
// Once the fix is in place, change this to:
//   } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
test_verify_one_file! {
    #[test] test_proof_with_lifetime_mismatch verus_code!{
        use vstd::prelude::*;
        // test expects a Tracked<&'a u64> where 'a is tied to param `a`
        fn test<'a>(a: &'a u64, b: u64) -> u64
        {
            let c: Tracked<&'a u64> = declare_with();
            1
        }

        // test2 has independent lifetimes 'a and 'b
        // Passing Tracked<&'b u64> where Tracked<&'a u64> is expected should fail
        fn test2<'a, 'b>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64
        {
            proof_with(c);
            test(a, b)
        }
    } => Err(err) => assert_vir_error_msg(err, "proof_with argument 1 has incompatible lifetime")
}

test_verify_one_file! {
    #[test] test_proof_with_lifetime_compatible verus_code!{
        use vstd::prelude::*;
        // Same as above, but 'b: 'a so the lifetime is compatible
        fn test<'a>(a: &'a u64, b: u64) -> u64
        {
            let c: Tracked<&'a u64> = declare_with();
            1
        }

        fn test2<'a, 'b: 'a>(a: &'a u64, b: u64, c: Tracked<&'b u64>) -> u64
        {
            proof_with(c);
            test(a, b)
        }
    } => Ok(())
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
            proof_with(c);
            test(a)
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
            proof_with(Tracked(0u64));
            proof_with(Ghost(2u32));
            test(0u64);
        }

        #[verifier(external)]
        fn unverified_call_test() {
            test(0u64);
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
            proof_with(Tracked(0u8));
            proof_with(Ghost(2u32));
            test(0u64);
        }

        #[verifier(external)]
        fn unverified_call_test() {
            test(0u64);
        }
     } => Err(e) => assert_vir_error_msg(e, "proof_with argument 1 has wrong type")
}
