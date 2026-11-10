#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_regression_78 verus_code! {
        use vstd::prelude::*;

        proof fn f1<T>(t: Ghost<Option<T>>) {
            let x = t.view()->0;
        }

        spec fn f2() -> bool {
            let x: Option<usize> = Option::None;
            x is None
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_regression_70 verus_code! {
        fn m(v: &mut u64) { }

        fn main() {
            let v = 6;
            m(&mut v);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `v` as mutable, as it is not declared as mutable")
}

test_verify_one_file! {
    #[test] ghost_stub_cfg_issue3157 verus_code! {
        mod m {
            pub fn helper() -> u8 {
                7
            }
        }

        use m::*;

        #[cfg(any())]
        proof fn helper() {
        }

        #[cfg_attr(all(), cfg(any()))]
        proof fn helper() {
        }

        #[test]
        proof fn helper() {
        }

        #[cfg_attr(all(), cfg_attr(all(), test, ignore))]
        proof fn helper() {
        }

        #[test]
        pub proof fn helper() {
        }

        proof fn helper() {
            #![cfg(any())]
        }

        #[cfg(any())]
        spec const helper: u8 = 1;

        fn test() -> u8 {
            helper()
        }

        fn test_nested() -> u8 {
            #[cfg(any())]
            proof fn helper() {
            }

            helper()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] private_broadcast_group_preserves_binding_pattern_issue3157 verus_code! {
        mod constants {
            pub const K: u8 = 1;
        }
        use constants::*;

        broadcast group K {}

        fn identity(x: u8) -> u8 {
            // If the group disappears, K becomes a constant and this match is not exhaustive.
            match x { K => K }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_stub_preserves_attrs_issue3157 verus_code! {
        #[deny(non_snake_case)]
        mod m {
            #[allow(non_snake_case)]
            #[verifier(external_body)]
            proof fn PrivateLemma() {}

            #[cfg_attr(all(), cfg_attr(all(), allow(non_snake_case)))]
            #[cfg_attr(verus_keep_ghost, verifier::external_body)]
            pub proof fn PublicLemma()
                ensures false,
            {
            }

            #[cfg_attr(all(), allow(non_snake_case))]
            pub broadcast group GhostGroup {}

            #[cfg_attr(any(), cfg_attr(all()))]
            proof fn inactive_malformed_attr() {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ghost_stub_malformed_cfg_attr_issue3157 code! {
        verus_erase_ghost! {
            // Intentionally malformed: cfg_attr requires a comma after the condition.
            // Erasure must preserve the attribute so rustc still reports the error.
            #[cfg_attr(all())]
            proof fn malformed_attr() {}
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(err.errors[0].message.contains("expected `,`, found end of `cfg_attr` input"));
    }
}
