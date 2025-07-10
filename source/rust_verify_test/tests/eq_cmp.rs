#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] eq_cmp1 verus_code! {
        use vstd::laws_eq::*;
        use vstd::laws_cmp::*;
        use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};
        use core::cmp::Ordering;

        fn test_eq<T: Ord>(x: &T, y: &T) -> (r: bool)
            requires
                obeys_cmp_spec::<T>(),
            ensures
                r <==> x.eq_spec(y),
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);

            if x.lt(y) {
                return false;
            }
            if x.gt(y) {
                return false;
            }
            true
        }

        fn test_eq_wrong<T: Ord>(x: &T, y: &T) -> (r: bool)
            requires
                obeys_cmp_spec::<T>(),
            ensures
                r <==> x.eq_spec(y),
        {
            reveal(obeys_cmp_partial_ord);
            reveal(obeys_cmp_ord);

            if x.lt(y) {
                return false;
            }
            if x.gt(y) {
                return true; // FAILS
            }
            true
        }

        fn test() {
            let b = test_eq(&Some(5u8), &Some(4u8 + 1));
            assert(b);

            let b = test_eq(&Some(5u8), &Some(4u8 - 1));
            assert(!b);
        }

        struct P(u8, bool);

        impl PartialEq for P {
            fn eq(&self, other: &P) -> (b: bool)
                ensures
                    b <==> self == other
            {
                self.0 == other.0 && self.1 == other.1
            }
        }
        impl vstd::std_specs::cmp::PartialEqSpecImpl for P {
            closed spec fn obeys_eq_spec() -> bool {
                true
            }

            closed spec fn eq_spec(&self, other: &P) -> bool {
                self == other
            }
        }
        impl Eq for P {
        }

        broadcast proof fn lemma_s_obeys_eq_spec()
            ensures
                #[trigger] obeys_eq_spec::<P>(),
        {
            reveal(obeys_eq_spec_properties);
        }

        broadcast proof fn lemma_s_obeys_concrete_eq()
            ensures
                #[trigger] obeys_concrete_eq::<P>(),
        {
            reveal(obeys_concrete_eq);
        }

        fn test_p_eq() {
            let b = P(3, true).eq(&P(3, false));
            assert(!b);
        }

        fn test_p_ee() {
            let b = P(3, true) == P(3, false);
            assert(!b);
        }

        #[derive(PartialEq, Eq, StructuralEq)]
        struct S(u8, bool);

        fn check_eq<T: Eq>(x: &T, y: &T) -> (b: bool)
            requires
                obeys_concrete_eq::<T>(),
            ensures
                b <==> x == y,
        {
            reveal(obeys_concrete_eq);
            x.eq(y)
        }

        fn test_s() {
            let b = check_eq(&S(3, true), &S(3, false));
            assert(!b);
            let b = S(3, true) == S(3, false);
            assert(!b);
        }
    } => Err(err) => assert_one_fails(err)
}
