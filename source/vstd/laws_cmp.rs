#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::laws_eq::*;
use super::prelude::*;
use super::std_specs::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};
use core::cmp::Ordering;

verus! {

#[verifier::opaque]
pub open spec fn obeys_partial_cmp_spec_properties<T: PartialOrd>() -> bool {
    &&& forall|x: T, y: T| #[trigger]
        x.partial_cmp_spec(&y) == Some(Ordering::Equal) <==> x.eq_spec(&y)
    &&& forall|x: T, y: T| #[trigger]
        x.partial_cmp_spec(&y) == Some(Ordering::Less) <==> y.partial_cmp_spec(&x) == Some(
            Ordering::Greater,
        )
    &&& forall|x: T, y: T, z: T|
        x.partial_cmp_spec(&y) == Some(Ordering::Less) && #[trigger] y.partial_cmp_spec(&z) == Some(
            Ordering::Less,
        ) ==> #[trigger] x.partial_cmp_spec(&z) == Some(Ordering::Less)
    &&& forall|x: T, y: T, z: T|
        x.partial_cmp_spec(&y) == Some(Ordering::Greater) && #[trigger] y.partial_cmp_spec(&z)
            == Some(Ordering::Greater) ==> #[trigger] x.partial_cmp_spec(&z) == Some(
            Ordering::Greater,
        )
    &&& obeys_eq_spec_properties::<T>()
}

#[verifier::opaque]
pub open spec fn obeys_cmp_partial_ord<T: PartialOrd>() -> bool {
    &&& T::obeys_eq_spec()
    &&& T::obeys_partial_cmp_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x.partial_cmp_spec(&y) == Some(Ordering::Equal)
}

#[verifier::opaque]
pub open spec fn obeys_cmp_ord<T: Ord>() -> bool {
    &&& T::obeys_cmp_spec()
    &&& forall|x: T, y: T|
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.cmp_spec(&y)]
        x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y))
}

pub open spec fn obeys_cmp<T: Ord>() -> bool {
    &&& obeys_eq::<T>()
    &&& obeys_cmp_partial_ord::<T>()
    &&& obeys_cmp_ord::<T>()
    &&& obeys_partial_cmp_spec_properties::<T>()
}

#[deprecated(note = "`laws_cmp::obeys_cmp_spec` has been renamed to `laws_cmp::obeys_cmp`")]
#[verifier::inline]
pub open spec fn obeys_cmp_spec<T: Ord>() -> bool {
    obeys_cmp::<T>()
}

macro_rules! num_laws_cmp {
    ($n: ty, $modname:ident) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_cmp_spec()
                ensures
                    #[trigger] obeys_cmp::<$n>(),
            {
                broadcast use group_laws_eq;
                reveal(obeys_eq_spec_properties);
                reveal(obeys_partial_cmp_spec_properties);
                reveal(obeys_cmp_partial_ord);
                reveal(obeys_cmp_ord);
                assert(obeys_eq::<$n>());
            }
        }
        }
    }
}

num_laws_cmp!(u8, u8_laws);

num_laws_cmp!(i8, i8_laws);

num_laws_cmp!(u16, u16_laws);

num_laws_cmp!(i16, i16_laws);

num_laws_cmp!(u32, u32_laws);

num_laws_cmp!(i32, i32_laws);

num_laws_cmp!(u64, u64_laws);

num_laws_cmp!(i64, i64_laws);

num_laws_cmp!(u128, u128_laws);

num_laws_cmp!(i128, i128_laws);

num_laws_cmp!(usize, usize_laws);

num_laws_cmp!(isize, isize_laws);

macro_rules! tuple_cmp_impl {
    ($modname:ident, $($T:ident )+) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_cmp_spec<$($T,)+>()
                where
                    $($T: Ord + PartialEq,)+
                requires
                    $(obeys_cmp::<$T>(),)+
                ensures
                    #[trigger] obeys_cmp::<($($T,)+)>(),
            {
                broadcast use group_laws_eq;
                reveal(obeys_eq_spec_properties);
                reveal(obeys_partial_cmp_spec_properties);
                reveal(obeys_cmp_partial_ord);
                reveal(obeys_cmp_ord);
                assert(obeys_cmp::<($($T,)+)>());
            }
        }
        }
    }
}

tuple_cmp_impl!(tuple_1_laws, T);

tuple_cmp_impl!(tuple_2_laws, U T);

proof fn lemma_isomorphic_obeys_cmp<T: PartialEq + Ord, U: PartialEq + Ord>(f: spec_fn(U) -> T)
    requires
        obeys_cmp::<T>(),
        obeys_eq::<U>(),
        U::obeys_partial_cmp_spec(),
        U::obeys_cmp_spec(),
        forall|x: U, y: U| x.eq_spec(&y) == f(x).eq_spec(&f(y)),
        forall|x: U, y: U| x.partial_cmp_spec(&y) == f(x).partial_cmp_spec(&f(y)),
        forall|x: U, y: U| x.cmp_spec(&y) == f(x).cmp_spec(&f(y)),
    ensures
        obeys_cmp::<U>(),
{
    reveal(obeys_eq_spec_properties);
    reveal(obeys_partial_cmp_spec_properties);
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
}

proof fn lemma_obeys_cmp_obeys_traits<T: Ord>()
    requires
        obeys_cmp::<T>(),
    ensures
        T::obeys_eq_spec(),
        T::obeys_partial_cmp_spec(),
        T::obeys_cmp_spec(),
{
    reveal(obeys_cmp_partial_ord);
    reveal(obeys_cmp_ord);
}

macro_rules! tuple_cmp_induct_impl {
    ($modname:ident, $inductmod:ident, 0 $U:ident, $($idx:tt $T:ident, )+) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_cmp_spec<$U, $($T,)+>()
                where
                    $U: Ord + PartialEq,
                    $($T: Ord + PartialEq,)+
                requires
                    obeys_cmp::<$U>(),
                    $(obeys_cmp::<$T>(),)+
                ensures
                    #[trigger] obeys_cmp::<($U, $($T,)+)>(),
            {
                broadcast use super::tuple_2_laws::lemma_obeys_cmp_spec;
                broadcast use super::$inductmod::lemma_obeys_cmp_spec;
                broadcast use group_laws_eq;
                lemma_obeys_cmp_obeys_traits::<$U>();
                $(lemma_obeys_cmp_obeys_traits::<$T>();)+
                lemma_isomorphic_obeys_cmp(|x: ($U, $($T,)+)| (x.0, ($(x.$idx,)+)));
                assert(obeys_cmp::<($U, $($T,)+)>());
            }
        }
        }
    };
}

tuple_cmp_induct_impl!(tuple_3_laws, tuple_2_laws, 0 V, 1 U, 2 T,);

tuple_cmp_induct_impl!(tuple_4_laws, tuple_3_laws, 0 X, 1 W, 2 V, 3 U, );

tuple_cmp_induct_impl!(tuple_5_laws, tuple_4_laws, 0 X, 1 W, 2 V, 3 U, 4 T, );

tuple_cmp_induct_impl!(tuple_6_laws, tuple_5_laws, 0 Y, 1 X, 2 W, 3 V, 4 U, 5 T, );

tuple_cmp_induct_impl!(tuple_7_laws, tuple_6_laws, 0 Z, 1 Y, 2 X, 3 W, 4 V, 5 U, 6 T, );

tuple_cmp_induct_impl!(tuple_8_laws, tuple_7_laws, 0 A, 1 Z, 2 Y, 3 X, 4 W, 5 V, 6 U, 7 T, );

tuple_cmp_induct_impl!(tuple_9_laws, tuple_8_laws, 0 B, 1 A, 2 Z, 3 Y, 4 X, 5 W, 6 V, 7 U, 8 T, );

tuple_cmp_induct_impl!(tuple_10_laws, tuple_9_laws, 0 C, 1 B, 2 A, 3 Z, 4 Y, 5 X, 6 W, 7 V, 8 U, 9 T, );

tuple_cmp_induct_impl!(tuple_11_laws, tuple_10_laws, 0 D, 1 C, 2 B, 3 A, 4 Z, 5 Y, 6 X, 7 W, 8 V, 9 U, 10 T, );

tuple_cmp_induct_impl!(tuple_12_laws, tuple_11_laws, 0 E, 1 D, 2 C, 3 B, 4 A, 5 Z, 6 Y, 7 X, 8 W, 9 V, 10 U, 11 T, );

pub broadcast proof fn lemma_ref_obeys_cmp_spec<T: Ord>()
    requires
        obeys_cmp::<T>(),
    ensures
        #[trigger] obeys_cmp::<&T>(),
{
    broadcast use lemma_ref_obeys_eq_spec;

    assert(obeys_eq::<&T>());

    assert(obeys_cmp_partial_ord::<&T>() && obeys_cmp_ord::<&T>()) by {
        reveal(obeys_cmp_partial_ord);
        reveal(obeys_cmp_ord);
    }

    assert(obeys_partial_cmp_spec_properties::<&T>()) by {
        reveal(obeys_cmp_partial_ord);
        reveal(obeys_partial_cmp_spec_properties);
    }
}

pub broadcast proof fn lemma_option_obeys_cmp_spec<T: Ord>()
    requires
        obeys_cmp::<T>(),
    ensures
        #[trigger] obeys_cmp::<Option<T>>(),
{
    broadcast use lemma_option_obeys_eq_spec;

    assert(obeys_eq::<Option<T>>());

    assert(obeys_cmp_partial_ord::<Option<T>>() && obeys_cmp_ord::<Option<T>>()) by {
        reveal(obeys_cmp_partial_ord);
        reveal(obeys_cmp_ord);
    }

    assert(obeys_partial_cmp_spec_properties::<Option<T>>()) by {
        reveal(obeys_cmp_partial_ord);
        reveal(obeys_partial_cmp_spec_properties);
    }
}

pub broadcast group group_laws_cmp {
    u8_laws::lemma_obeys_cmp_spec,
    i8_laws::lemma_obeys_cmp_spec,
    u16_laws::lemma_obeys_cmp_spec,
    i16_laws::lemma_obeys_cmp_spec,
    u32_laws::lemma_obeys_cmp_spec,
    i32_laws::lemma_obeys_cmp_spec,
    u64_laws::lemma_obeys_cmp_spec,
    i64_laws::lemma_obeys_cmp_spec,
    u128_laws::lemma_obeys_cmp_spec,
    i128_laws::lemma_obeys_cmp_spec,
    usize_laws::lemma_obeys_cmp_spec,
    isize_laws::lemma_obeys_cmp_spec,
    lemma_ref_obeys_cmp_spec,
    lemma_option_obeys_cmp_spec,
    tuple_1_laws::lemma_obeys_cmp_spec,
    tuple_2_laws::lemma_obeys_cmp_spec,
    tuple_3_laws::lemma_obeys_cmp_spec,
    tuple_4_laws::lemma_obeys_cmp_spec,
    tuple_5_laws::lemma_obeys_cmp_spec,
    tuple_6_laws::lemma_obeys_cmp_spec,
    tuple_7_laws::lemma_obeys_cmp_spec,
    tuple_8_laws::lemma_obeys_cmp_spec,
    tuple_9_laws::lemma_obeys_cmp_spec,
    tuple_10_laws::lemma_obeys_cmp_spec,
    tuple_11_laws::lemma_obeys_cmp_spec,
    tuple_12_laws::lemma_obeys_cmp_spec,
}

} // verus!
