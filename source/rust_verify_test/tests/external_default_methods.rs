#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// An impl that rustc confirms inherits an external trait's default receives the
// `default_ensures` contract, including for defaults with method-level generics,
// both at direct calls and through `call_ensures`.
test_verify_one_file! {
    #[test] inherited_external_default_with_method_generics verus_code! {
        #[verifier::external]
        pub trait Trait: Sized {
            fn generic_default<C>(&self, c: C) -> u64 { 7 }
        }

        #[verifier::external_trait_specification]
        pub trait ExTrait: Sized {
            type ExternalTraitSpecificationFor: Trait;

            fn generic_default<C>(&self, c: C) -> (result: u64)
                default_ensures result == 7;
        }

        pub struct S;
        impl Trait for S {}

        fn direct(x: &S) {
            let r = x.generic_default(true);
            assert(r == 7);
        }

        proof fn reflected(x: &S, r: u64)
            requires call_ensures(S::generic_default::<bool>, (x, true), r),
            ensures r == 7,
        {}
    } => Ok(())
}

// Std impls that rustc confirms inherit a default now receive vstd's
// `default_ensures` for that default. Option<u64> inherits both PartialEq::ne
// and PartialOrd::lt from core, so the contracts in std_specs/cmp.rs apply.
test_verify_one_file! {
    #[test] inherited_comparison_defaults verus_code! {
        use vstd::prelude::*;
        use core::cmp::Ordering;

        proof fn inherited(a: Option<u64>, b: Option<u64>) {
            assert(forall|result: bool| call_ensures(Option::<u64>::ne, (&a, &b), result) ==>
                call_ensures(Option::<u64>::eq, (&a, &b), !result));
            assert(forall|result: bool| call_ensures(Option::<u64>::lt, (&a, &b), result) ==>
                exists|o: Option<Ordering>|
                    call_ensures(Option::<u64>::partial_cmp, (&a, &b), o)
                        && result == (o == Some(Ordering::Less)));
        }
    } => Ok(())
}

// core overrides `ne` for the primitive integers, so the `default_ensures`
// relating `ne` to `eq` must not apply to them.
test_verify_one_file! {
    #[test] primitive_override_does_not_supply_default_facts verus_code! {
        use vstd::prelude::*;
        use core::cmp::PartialEq;

        spec fn ne_contract<T: PartialEq>(a: &T, b: &T, result: bool) -> bool {
            call_ensures(T::ne, (a, b), result)
        }

        proof fn test(a: &u64, b: &u64, result: bool)
            requires ne_contract(a, b, result),
            ensures call_ensures(u64::eq, (a, b), !result), // FAILS
        {}
    } => Err(err) => assert_one_fails(err)
}
