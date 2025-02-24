#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_coercion_not_allowed_in_spec verus_code! {
        use vstd::prelude::*;

        spec fn stuff(x: Option<u64>) -> u64 {
            match x {
                Some(x) => x,
                None => {
                    arbitrary::<!>()
                }
            }
        }
    } => Err(e) => assert_vir_error_msg(e, "never-to-any coercion is not allowed in spec mode")
}

test_verify_one_file! {
    #[test] coercion_in_exec verus_code! {
        enum Option<V> {
            Some(V),
            None,
        }

        fn never_returns() -> ! {
            loop { }
        }

        fn stuff(x: Option<u64>) -> (res: u64)
            ensures x == Option::Some(res)
        {
            match x {
                Option::Some(x) => x,
                Option::None => never_returns(),
            }
        }

        fn stuff_fails(x: Option<u64>) -> (res: u64)
            ensures x == Option::Some(res)
        {
            let x = match x {
                Option::Some(x) => x,
                Option::None => never_returns(),
            }
            assert(false); // FAILS
            x
        }
    } => Err(e) => assert_fails(e, 1)
}

test_verify_one_file! {
    #[test] coercion_in_proof_mode verus_code! {
        struct X { }

        proof fn takes_x(tracked x: X) { }

        #[verifier::external_body]
        proof fn never_returns() -> (tracked t: !) {
            loop { }
        }

        #[allow(unreachable_code)]
        proof fn test() {
            takes_x(never_returns());
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_spec_never_caught1 verus_code! {
        spec fn make_never() -> !;
        proof fn test() {
            let x: ! = make_never();
            let y: ! = make_never();
            assert(x == y);
            let tracked z = x; // FAILS
            assert(false); // FAILS
        }
    } => Err(e) => assert_vir_error_msg(e, "never-to-any coercion is not allowed in spec mode")
}

test_verify_one_file! {
    #[test] test_spec_never_caught2 verus_code! {
        spec fn make_never() -> !;
        proof fn test() {
            let x: ! = make_never();
            let y: ! = make_never();
            let tracked t: ! = true; // FAILS
        }
    } => Err(e) => assert_rust_error_msg(e, "mismatched types")
}

test_verify_one_file! {
    #[test] test_spec_never_caught3 verus_code! {
        spec fn make_never() -> !;
        fn test_exec() -> ! {
            let ghost x = make_never();
        }
    } => Err(e) => assert_vir_error_msg(e, "never-to-any coercion is not allowed in spec mode")
}
