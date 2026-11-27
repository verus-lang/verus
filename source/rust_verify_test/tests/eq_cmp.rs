#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] borrowed_cmp_matches verus_code! {
        use vstd::std_specs::borrow::BorrowSpec;
        use vstd::std_specs::cmp::{borrowed_key_ordering_matches, OrdSpec};

        proof fn references<T: Ord + ?Sized>(x: &T, y: &T) {
            assert(borrowed_key_ordering_matches::<&T, T>());
            assert(<&T as OrdSpec>::cmp_spec(&x, &y)
                == <&T as BorrowSpec<T>>::borrow_spec(&x).cmp_spec(
                    <&T as BorrowSpec<T>>::borrow_spec(&y)));
        }

        proof fn self_borrow<T: Ord>() {
            assert(borrowed_key_ordering_matches::<T, T>());
            assert(vstd::std_specs::btree::borrowed_key_ordering_matches::<T, T>());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] borrowed_cmp_requires_compatibility verus_code! {
        use std::borrow::Borrow;
        use vstd::std_specs::cmp::borrowed_key_ordering_matches;

        proof fn arbitrary_borrow<T: Borrow<U> + Ord, U: Ord + ?Sized>() {
            assert(borrowed_key_ordering_matches::<T, U>()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] eq_cmp1 verus_code! {
        use vstd::laws_eq::*;
        use vstd::laws_cmp::*;
        use vstd::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};
        use core::cmp::Ordering;

        fn test_eq<T: Ord>(x: &T, y: &T) -> (r: bool)
            requires
                obeys_cmp::<T>(),
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
                obeys_cmp::<T>(),
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
                #[trigger] obeys_eq::<P>(),
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

test_verify_one_file! {
    // https://github.com/verus-lang/verus/issues/3167
    #[test] ord_max_default verus_code! {
        use core::cmp::Ordering;
        use vstd::std_specs::cmp::*;

        #[derive(PartialEq, Eq)]
        pub struct S {
            pub v: u8,
        }

        impl PartialOrd for S {
            fn partial_cmp(&self, other: &S) -> (r: Option<Ordering>) {
                None
            }
        }

        impl PartialOrdSpecImpl for S {
            open spec fn obeys_partial_cmp_spec() -> bool {
                true
            }

            open spec fn partial_cmp_spec(&self, other: &S) -> Option<Ordering> {
                None
            }
        }

        impl Ord for S {
            fn cmp(&self, other: &S) -> (r: Ordering) {
                if self.v < other.v {
                    Ordering::Less
                } else if self.v == other.v {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }

        impl OrdSpecImpl for S {
            open spec fn obeys_cmp_spec() -> bool {
                true
            }

            open spec fn cmp_spec(&self, other: &S) -> Ordering {
                if self.v < other.v {
                    Ordering::Less
                } else if self.v == other.v {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }

        fn test() {
            let m = (S { v: 5 }).max(S { v: 3 });
            assert(m.v == 5); // FAILS
            assert(false);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cmp_min_max verus_code! {
        use core::cmp::Ordering;
        use vstd::std_specs::cmp::{OrdSpec, PartialOrdSpec};

        fn test_ints(a: u32, b: u32, c: i8, d: i8) {
            let m = core::cmp::min(a, b);
            assert(m == if a <= b { a } else { b });
            let m = core::cmp::max(a, b);
            assert(m == if a <= b { b } else { a });
            let lo = core::cmp::min(c, d);
            let hi = core::cmp::max(c, d);
            assert(lo <= hi);
        }

        // On a tie, `min` returns its first argument and `max` its second.
        fn test_generic<T: Ord + Copy>(a: T, b: T) -> (r: (T, T))
            requires
                T::obeys_cmp_spec(),
                T::obeys_partial_cmp_spec(),
                b.partial_cmp_spec(&a) == Some(b.cmp_spec(&a)),
            ensures
                r.0 == if b.cmp_spec(&a) == Ordering::Less { b } else { a },
                r.1 == if b.cmp_spec(&a) == Ordering::Less { a } else { b },
        {
            (core::cmp::min(a, b), core::cmp::max(a, b))
        }

        // Without the cmp laws, `T` may override `Ord::min` with anything.
        fn test_generic_unconstrained<T: Ord + Copy>(a: T, b: T) {
            let m = core::cmp::min(a, b);
            assert(m == a || m == b); // FAILS
        }

        #[derive(PartialEq, Eq)]
        pub struct S {
            pub v: u8,
        }

        impl PartialOrd for S {
            fn partial_cmp(&self, other: &S) -> (r: Option<Ordering>) {
                None
            }
        }

        impl vstd::std_specs::cmp::PartialOrdSpecImpl for S {
            open spec fn obeys_partial_cmp_spec() -> bool {
                true
            }

            open spec fn partial_cmp_spec(&self, other: &S) -> Option<Ordering> {
                None
            }
        }

        impl Ord for S {
            fn cmp(&self, other: &S) -> (r: Ordering) {
                if self.v < other.v {
                    Ordering::Less
                } else if self.v == other.v {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }

        impl vstd::std_specs::cmp::OrdSpecImpl for S {
            open spec fn obeys_cmp_spec() -> bool {
                true
            }

            open spec fn cmp_spec(&self, other: &S) -> Ordering {
                if self.v < other.v {
                    Ordering::Less
                } else if self.v == other.v {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }

        // Like `Ord::max` and `Ord::min` (see `ord_max_default`), `max` and
        // `min` decide with `<`, which uses `partial_cmp`, not `cmp`.
        fn test_inconsistent() {
            let m = core::cmp::max(S { v: 5 }, S { v: 3 });
            assert(m.v == 3);
            let m = core::cmp::min(S { v: 5 }, S { v: 3 });
            assert(m.v == 5);
        }

        fn test_inconsistent_fails() {
            let m = core::cmp::max(S { v: 5 }, S { v: 3 });
            assert(m.v == 5); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] cmp_min_by_max_by verus_code! {
        use core::cmp::Ordering;
        use vstd::std_specs::cmp::OrdSpec;

        fn cmp_first(x: &(u8, u8), y: &(u8, u8)) -> (o: Ordering)
            ensures
                o == x.0.cmp_spec(&y.0),
        {
            x.0.cmp(&y.0)
        }

        fn test() {
            // On a tie, `min_by` returns its first argument and `max_by` its second.
            let r = core::cmp::min_by((1u8, 1u8), (1u8, 2u8), cmp_first);
            assert(r == (1u8, 1u8));
            let r = core::cmp::max_by((1u8, 1u8), (1u8, 2u8), cmp_first);
            assert(r == (1u8, 2u8));
            let r = core::cmp::min_by((2u8, 0u8), (1u8, 5u8), cmp_first);
            assert(r == (1u8, 5u8));
            let r = core::cmp::max_by((2u8, 0u8), (1u8, 5u8), cmp_first);
            assert(r == (2u8, 0u8));
            // `compare` is called as `compare(&v1, &v2)`.
            let r = core::cmp::min_by(1u8, 2u8, |x: &u8, y: &u8| -> (o: Ordering)
                requires
                    *x == 1 && *y == 2,
                ensures
                    o == Ordering::Greater,
                {
                    Ordering::Greater
                });
            assert(r == 2);
        }

        fn test_tie_min_by_fails() {
            let r = core::cmp::min_by((1u8, 1u8), (1u8, 2u8), cmp_first);
            assert(r == (1u8, 2u8)); // FAILS
        }

        fn test_tie_max_by_fails() {
            let r = core::cmp::max_by((1u8, 1u8), (1u8, 2u8), cmp_first);
            assert(r == (1u8, 1u8)); // FAILS
        }

        fn test_requires_fails() {
            let r = core::cmp::max_by(2u8, 1u8, |x: &u8, y: &u8| -> (o: Ordering)
                requires
                    *x == 1,
                {
                    x.cmp(y)
                }); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] cmp_min_by_key_max_by_key verus_code! {
        use vstd::prelude::*;

        fn test() {
            let first = |x: &(u8, u8)| -> (k: u8)
                ensures
                    k == x.0,
                {
                    x.0
                };
            // On a tie, `min_by_key` returns its first argument and `max_by_key` its second.
            let r = core::cmp::min_by_key((1u8, 1u8), (1u8, 2u8), first);
            assert(r == (1u8, 1u8));
            let r = core::cmp::max_by_key((1u8, 1u8), (1u8, 2u8), first);
            assert(r == (1u8, 2u8));
            let r = core::cmp::min_by_key((2u8, 0u8), (1u8, 5u8), first);
            assert(r == (1u8, 5u8));
            let r = core::cmp::max_by_key((2u8, 0u8), (1u8, 5u8), first);
            assert(r == (2u8, 0u8));
        }

        fn test_tie_min_by_key_fails() {
            let first = |x: &(u8, u8)| -> (k: u8)
                ensures
                    k == x.0,
                {
                    x.0
                };
            let r = core::cmp::min_by_key((1u8, 1u8), (1u8, 2u8), first);
            assert(r == (1u8, 2u8)); // FAILS
        }

        fn test_tie_max_by_key_fails() {
            let first = |x: &(u8, u8)| -> (k: u8)
                ensures
                    k == x.0,
                {
                    x.0
                };
            let r = core::cmp::max_by_key((1u8, 1u8), (1u8, 2u8), first);
            assert(r == (1u8, 1u8)); // FAILS
        }

        // `f` is called on both arguments.
        fn test_requires_fails() {
            let r = core::cmp::max_by_key(1u8, 0u8, |x: &u8| -> (k: u8)
                requires
                    *x != 0,
                {
                    *x
                }); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

// A PartialEqSpecImpl impl attaches specs to the matching PartialEq impl.
// If that PartialEq impl is not verified, the PartialEqSpecImpl impl is an assumption,
// which must be marked with #[verifier::assume_external_impl]
// (https://github.com/verus-lang/verus/issues/3208)

test_verify_one_file! {
    #[test] spec_impl_for_impl_outside_verus_macro code! {
        use vstd::prelude::*;
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        verus! {
        pub struct S {
            pub x: u8,
        }
        }

        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                false
            }
        }

        verus! {
        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                true
            }
        }

        fn test() -> (r: bool)
            ensures
                r,
        {
            let a = S { x: 1 };
            a.eq(&a)
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "so the specifications in this impl are unverified assumptions")
}

test_verify_one_file! {
    #[test] spec_impl_for_external_impl verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        pub struct S {
            pub x: u8,
        }

        #[verifier::external]
        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                false
            }
        }

        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "so the specifications in this impl are unverified assumptions")
}

test_verify_one_file! {
    #[test] spec_impl_for_external_impl_generic verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        pub struct S<A> {
            pub x: A,
        }

        #[verifier::external]
        impl<A> PartialEq for S<A> {
            fn eq(&self, other: &S<A>) -> bool {
                false
            }
        }

        impl<A> PartialEqSpecImpl for S<A> {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S<A>) -> bool {
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "so the specifications in this impl are unverified assumptions")
}

test_verify_one_file! {
    #[test] spec_impl_for_external_iterator verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::iter::IteratorSpecImpl;

        pub struct Counter {
            pub n: u8,
        }

        #[verifier::external]
        impl Iterator for Counter {
            type Item = u8;
            fn next(&mut self) -> Option<u8> {
                None
            }
        }

        impl IteratorSpecImpl for Counter {
            open spec fn obeys_prophetic_iter_laws(&self) -> bool {
                true
            }

            #[verifier::prophetic]
            open spec fn remaining(&self) -> Seq<u8> {
                seq![1]
            }

            #[verifier::prophetic]
            open spec fn produces(&self) -> Seq<bool> {
                seq![true]
            }

            open spec fn decrease(&self) -> Option<nat> {
                None
            }

            open spec fn peek(&self, index: int) -> Option<u8> {
                None
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "so the specifications in this impl are unverified assumptions")
}

test_verify_one_file! {
    #[test] spec_impl_for_external_impl_assumed code! {
        use vstd::prelude::*;
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        verus! {
        pub struct S {
            pub x: u8,
        }
        }

        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                self.x == other.x
            }
        }

        verus! {
        #[verifier::assume_external_impl]
        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                self.x == other.x
            }
        }

        fn test() -> (r: bool)
            ensures
                r,
        {
            let a = S { x: 1 };
            a.eq(&a)
        }

        fn test_fail() -> (r: bool)
            ensures
                !r, // FAILS
        {
            let a = S { x: 1 };
            a.eq(&a)
        }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] spec_impl_for_external_impl_assumed_no_cheating ["--no-cheating"] => verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        pub struct S {
            pub x: u8,
        }

        #[verifier::external]
        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                self.x == other.x
            }
        }

        #[verifier::assume_external_impl]
        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                self.x == other.x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_external_impl]` not allowed with `--no-cheating`")
}

test_verify_one_file_with_options! {
    #[test] structural_eq_derive_no_cheating ["--no-cheating"] => verus_code! {
        use vstd::prelude::*;

        #[derive(PartialEq, Eq, StructuralEq)]
        pub struct S {
            pub x: u8,
        }

        fn test(a: S, b: S) {
            let r = a == b;
            assert(r == (a == b));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] spec_impl_for_external_impl_assumed_automatically_derived_no_cheating ["--no-cheating"] => verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        pub struct S {
            pub x: u8,
        }

        #[verifier::external]
        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                self.x == other.x
            }
        }

        // a hand-written #[automatically_derived] does not get the StructuralEq exemption
        #[automatically_derived]
        #[verifier::assume_external_impl]
        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                self.x == other.x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_external_impl]` not allowed with `--no-cheating`")
}

test_verify_one_file_with_options! {
    #[test] spec_impl_for_external_impl_assumed_no_cheating_trusted ["--no-cheating"] => verus_code! {
        #[verus::trusted]
        mod trusted {
            use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

            pub struct S {
                pub x: u8,
            }

            #[verifier::external]
            impl PartialEq for S {
                fn eq(&self, other: &S) -> bool {
                    self.x == other.x
                }
            }

            #[verifier::assume_external_impl]
            impl PartialEqSpecImpl for S {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &S) -> bool {
                    self.x == other.x
                }
            }
        }

        fn test(a: trusted::S, b: trusted::S) {
            let r = a == b;
            assert(r == (a.x == b.x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] spec_impl_for_verified_impl_assumed verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialEqSpecImpl};

        pub struct S {
            pub x: u8,
        }

        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                self.x == other.x
            }
        }

        #[verifier::assume_external_impl]
        impl PartialEqSpecImpl for S {
            open spec fn obeys_eq_spec() -> bool {
                true
            }

            open spec fn eq_spec(&self, other: &S) -> bool {
                self.x == other.x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_external_impl]` is unnecessary")
}

test_verify_one_file! {
    #[test] assume_external_impl_on_inherent_impl verus_code! {
        pub struct S {
            pub x: u8,
        }

        #[verifier::assume_external_impl]
        impl S {
            fn get(&self) -> u8 {
                self.x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_external_impl]` is only allowed on impls of external trait extensions")
}

test_verify_one_file! {
    #[test] assume_external_impl_on_non_extension_impl verus_code! {
        pub struct S {
            pub x: u8,
        }

        #[verifier::assume_external_impl]
        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                self.x == other.x
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "`#[verifier::assume_external_impl]` is only allowed on impls of external trait extensions")
}

test_verify_one_file! {
    #[test] external_impl_without_spec_impl verus_code! {
        // An unverified impl with no matching PartialEqSpecImpl impl only gets
        // the default (uninformative) specs, so no attribute is needed
        use vstd::std_specs::cmp::PartialEqSpec;

        pub struct S {
            pub x: u8,
        }

        #[verifier::external]
        impl PartialEq for S {
            fn eq(&self, other: &S) -> bool {
                false
            }
        }

        fn test() {
            let a = S { x: 1 };
            let b = a.eq(&a);
            assert(b); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
