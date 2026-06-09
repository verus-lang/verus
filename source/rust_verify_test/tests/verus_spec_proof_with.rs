#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// =============================================================================
// Tests for #[verus_spec(with ...)] and proof_with!{} in various contexts:
// - external functions with external_fn_specification
// - functions across modules
// - trait methods
// - generic functions
// - declare_ret_with (extra ghost/tracked outputs)
// =============================================================================

// --- External function with declare_with via external_fn_specification ---

test_verify_one_file! {
    #[test] test_external_fn_with_declare_with code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
                -> z: Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
                z@ == extra,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_external_proof_with() {
            proof_decl!{
                let tracked z;
            }
            proof_with!{Tracked(1u8) => Tracked(z): Tracked<u32>}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
                assert(z == 1u8);
            }

            proof_with!{Tracked(1u8)}
            let ret = negate_bool(true, 1);
            proof!{
                assert(!ret);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    // Calling an external function with declare_with but missing proof_with should fail
    #[test] test_external_fn_missing_proof_with code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_external_no_proof_with() {
            let ret = negate_bool(true, 1); // should fail
        }
    } => Err(e) => assert_vir_error_msg(e, "proof_with()")
}

test_verify_one_file! {
    // Calling an external function with wrong requires should fail verification
    #[test] test_external_fn_failed_requires code!{
        #[verifier::external]
        fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier::external_fn_specification]
        #[verus_spec(ret =>
            with
                Tracked(extra): Tracked<u8>
            requires
                x == extra,
            ensures
                ret == !b,
        )]
        fn negate_bool_requires_ensures(b: bool, x: u8) -> bool {
            negate_bool(b, x)
        }

        #[verus_spec]
        fn test_call_wrong_requires() {
            proof_with!{Tracked(99u8)}
            let ret = negate_bool(true, 1); // FAILS: x=1 != extra@=99
        }
    } => Err(e) => assert_one_fails(e)
}

// --- Functions in different modules ---

test_verify_one_file! {
    #[test] test_cross_module_proof_with code!{
        mod inner {
            use vstd::prelude::*;

            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                requires
                    a < 100 && extra@ < 100,
                ensures
                    ret == a,
            )]
            pub fn copy_u64(a: u64) -> u64
            {
                a
            }
        }

        #[verus_spec]
        fn test_call_cross_module() {
            use vstd::prelude::*;
            use inner::copy_u64;
            proof_with!{Ghost(5u64)}
            let ret = copy_u64(10);
            proof!{assert(ret == 10);}
        }
    } => Ok(())
}

// TODO: update verus_spec macro to support trait methods
test_verify_one_file! {
    #[test] test_trait_method code!{
        use vstd::prelude::*;

        #[verus_verify]
        trait X {
            #[verus_spec(ret=>
                with
                    Ghost(extra): Ghost<u64>,
                requires
                    a < 100 && extra@ < 100,
                ensures
                    ret == a,
            )]
            fn copy_u64(&self, a: u64) -> u64;
        }
    } => Err(e) => assert_any_vir_error_msg(e, "`with` does not support trait")
}
