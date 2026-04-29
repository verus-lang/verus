#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use super::std_specs::cmp::PartialEqSpec;
use super::view::*;

verus! {

#[verifier::opaque]
pub open spec fn obeys_eq_spec_properties<T: PartialEq>() -> bool {
    &&& forall|x: T, y: T| #[trigger] x.eq_spec(&y) <==> y.eq_spec(&x)
    &&& forall|x: T, y: T, z: T|
        x.eq_spec(&y) && #[trigger] y.eq_spec(&z) ==> #[trigger] x.eq_spec(&z)
}

pub open spec fn obeys_eq<T: PartialEq>() -> bool {
    &&& T::obeys_eq_spec()
    &&& obeys_eq_spec_properties::<T>()
}

#[deprecated(note = "`laws_eq::obeys_eq_spec` has been renamed to `laws_eq::obeys_eq`")]
#[verifier::inline]
pub open spec fn obeys_eq_spec<T: PartialEq>() -> bool {
    obeys_eq::<T>()
}

#[verifier::opaque]
pub open spec fn obeys_concrete_eq<T: PartialEq>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x == y
}

#[verifier::opaque]
pub open spec fn obeys_view_eq<T: PartialEq + View>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x@ == y@
}

#[verifier::opaque]
pub open spec fn obeys_deep_eq<T: PartialEq + DeepView>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x.deep_view() == y.deep_view()
}

pub broadcast proof fn axiom_structural_obeys_concrete_eq<T: PartialEq + Structural>()
    requires
        T::obeys_eq_spec(),
        forall|x: T, y: T| x.eq_spec(&y) <==> x == y,
    ensures
        #[trigger] obeys_concrete_eq::<T>(),
{
    reveal(obeys_concrete_eq);
}

macro_rules! primitive_laws_eq {
    ($n: ty, $modname:ident) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_eq_spec()
                ensures
                    #[trigger] obeys_eq::<$n>(),
            {
                reveal(obeys_eq_spec_properties);
            }

            pub broadcast proof fn lemma_obeys_concrete_eq()
                ensures
                    #[trigger] obeys_concrete_eq::<$n>(),
            {
                reveal(obeys_concrete_eq);
            }

            pub broadcast proof fn lemma_obeys_view_eq()
                ensures
                    #[trigger] obeys_view_eq::<$n>(),
            {
                reveal(obeys_view_eq);
            }

            pub broadcast proof fn lemma_obeys_deep_eq()
                ensures
                    #[trigger] obeys_deep_eq::<$n>(),
            {
                reveal(obeys_deep_eq);
            }

            pub broadcast group group_laws_eq {
                lemma_obeys_eq_spec,
                lemma_obeys_concrete_eq,
                lemma_obeys_view_eq,
                lemma_obeys_deep_eq,
            }
        }
        }
    }
}

primitive_laws_eq!(bool, bool_laws);

primitive_laws_eq!(u8, u8_laws);

primitive_laws_eq!(i8, i8_laws);

primitive_laws_eq!(u16, u16_laws);

primitive_laws_eq!(i16, i16_laws);

primitive_laws_eq!(u32, u32_laws);

primitive_laws_eq!(i32, i32_laws);

primitive_laws_eq!(u64, u64_laws);

primitive_laws_eq!(i64, i64_laws);

primitive_laws_eq!(u128, u128_laws);

primitive_laws_eq!(i128, i128_laws);

primitive_laws_eq!(usize, usize_laws);

primitive_laws_eq!(isize, isize_laws);

macro_rules! tuple_eq_impl {
    ($modname:ident, $($T:ident )+) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_eq_spec<$($T,)+>()
                where
                    $($T: PartialEq,)+
                requires
                    $(obeys_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_eq::<($($T,)+)>(),
            {
                reveal(obeys_eq_spec_properties);
            }

            pub broadcast proof fn lemma_obeys_concrete_eq<$($T,)+>()
                where
                    $($T: PartialEq,)+
                requires
                    $(obeys_concrete_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_concrete_eq::<($($T,)+)>(),
            {
                reveal(obeys_concrete_eq);
            }

            pub broadcast proof fn lemma_obeys_view_eq<$($T,)+>()
                where
                    $($T: PartialEq + View,)+
                requires
                    $(obeys_view_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_view_eq::<($($T,)+)>(),
            {
                reveal(obeys_view_eq);
            }

            pub broadcast proof fn lemma_obeys_deep_eq<$($T,)+>()
                where
                    $($T: PartialEq + DeepView,)+
                requires
                    $(obeys_deep_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_deep_eq::<($($T,)+)>(),
            {
                reveal(obeys_deep_eq);
            }

            pub broadcast group group_laws_eq {
                lemma_obeys_eq_spec,
                lemma_obeys_concrete_eq,
                lemma_obeys_view_eq,
                lemma_obeys_deep_eq,
            }
        }
        }
    }
}

tuple_eq_impl!(tuple_1_laws, T);

tuple_eq_impl!(tuple_2_laws, U T);

proof fn lemma_isomorphic_obeys_eq<T: PartialEq, U: PartialEq>(f: spec_fn(U) -> T)
    requires
        obeys_eq::<T>(),
        U::obeys_eq_spec(),
        forall|x: U, y: U| x.eq_spec(&y) == f(x).eq_spec(&f(y)),
    ensures
        obeys_eq::<U>(),
{
    reveal(obeys_eq_spec_properties);
}

macro_rules! tuple_eq_induct_impl {
    ($modname:ident, $inductmod:ident, 0 $U:ident, $($idx:tt $T:ident, )+) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_eq_spec<$U, $($T,)+>()
                where
                    $U: PartialEq,
                    $($T: PartialEq,)+
                requires
                    obeys_eq::<$U>(),
                    $(obeys_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_eq::<($U, $($T,)+)>(),
            {
                broadcast use tuple_2_laws::lemma_obeys_eq_spec;
                broadcast use $inductmod::lemma_obeys_eq_spec;
                lemma_isomorphic_obeys_eq(|x: ($U, $($T,)+)| (x.0, ($(x.$idx,)+)));
                reveal(obeys_eq_spec_properties);
            }

            pub broadcast proof fn lemma_obeys_concrete_eq<$U, $($T,)+>()
                where
                    $U: PartialEq,
                    $($T: PartialEq,)+
                requires
                    obeys_concrete_eq::<$U>(),
                    $(obeys_concrete_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_concrete_eq::<($U, $($T,)+)>(),
            {
                reveal(obeys_concrete_eq);
            }

            pub broadcast proof fn lemma_obeys_view_eq<$U, $($T,)+>()
                where
                    $U: PartialEq + View,
                    $($T: PartialEq + View,)+
                requires
                    obeys_view_eq::<$U>(),
                    $(obeys_view_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_view_eq::<($U, $($T,)+)>(),
            {
                broadcast use tuple_2_laws::group_laws_eq;
                broadcast use $inductmod::group_laws_eq;
                reveal(obeys_view_eq);
            }

            pub broadcast proof fn lemma_obeys_deep_eq<$U, $($T,)+>()
                where
                    $U: PartialEq + DeepView,
                    $($T: PartialEq + DeepView,)+
                requires
                    obeys_deep_eq::<$U>(),
                    $(obeys_deep_eq::<$T>(),)+
                ensures
                    #[trigger] obeys_deep_eq::<($U, $($T,)+)>(),
            {
                broadcast use tuple_2_laws::group_laws_eq;
                broadcast use $inductmod::group_laws_eq;
                reveal(obeys_deep_eq);
            }

            pub broadcast group group_laws_eq {
                lemma_obeys_eq_spec,
                lemma_obeys_concrete_eq,
                lemma_obeys_view_eq,
                lemma_obeys_deep_eq,
            }
        }
        }
    };
}

tuple_eq_induct_impl!(tuple_3_laws, tuple_2_laws, 0 V, 1 U, 2 T,);

tuple_eq_induct_impl!(tuple_4_laws, tuple_3_laws, 0 X, 1 W, 2 V, 3 U, );

tuple_eq_induct_impl!(tuple_5_laws, tuple_4_laws, 0 X, 1 W, 2 V, 3 U, 4 T, );

tuple_eq_induct_impl!(tuple_6_laws, tuple_5_laws, 0 Y, 1 X, 2 W, 3 V, 4 U, 5 T, );

tuple_eq_induct_impl!(tuple_7_laws, tuple_6_laws, 0 Z, 1 Y, 2 X, 3 W, 4 V, 5 U, 6 T, );

tuple_eq_induct_impl!(tuple_8_laws, tuple_7_laws, 0 A, 1 Z, 2 Y, 3 X, 4 W, 5 V, 6 U, 7 T, );

tuple_eq_induct_impl!(tuple_9_laws, tuple_8_laws, 0 B, 1 A, 2 Z, 3 Y, 4 X, 5 W, 6 V, 7 U, 8 T, );

tuple_eq_induct_impl!(tuple_10_laws, tuple_9_laws, 0 C, 1 B, 2 A, 3 Z, 4 Y, 5 X, 6 W, 7 V, 8 U, 9 T, );

tuple_eq_induct_impl!(tuple_11_laws, tuple_10_laws, 0 D, 1 C, 2 B, 3 A, 4 Z, 5 Y, 6 X, 7 W, 8 V, 9 U, 10 T, );

tuple_eq_induct_impl!(tuple_12_laws, tuple_11_laws, 0 E, 1 D, 2 C, 3 B, 4 A, 5 Z, 6 Y, 7 X, 8 W, 9 V, 10 U, 11 T, );

/* references */

pub broadcast proof fn lemma_ref_obeys_eq_spec<T: PartialEq>()
    requires
        obeys_eq::<T>(),
    ensures
        #[trigger] obeys_eq::<&T>(),
{
    reveal(obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_ref_obeys_concrete_eq<T: PartialEq>()
    requires
        obeys_concrete_eq::<T>(),
    ensures
        #[trigger] obeys_concrete_eq::<&T>(),
{
    reveal(obeys_concrete_eq);
}

pub broadcast proof fn lemma_ref_obeys_view_eq<T: PartialEq + View>()
    requires
        obeys_view_eq::<T>(),
    ensures
        #[trigger] obeys_view_eq::<&T>(),
{
    reveal(obeys_view_eq);
}

pub broadcast proof fn lemma_ref_obeys_deep_eq<T: PartialEq + DeepView>()
    requires
        obeys_deep_eq::<T>(),
    ensures
        #[trigger] obeys_deep_eq::<&T>(),
{
    reveal(obeys_deep_eq);
}

/* Option */

pub broadcast proof fn lemma_option_obeys_eq_spec<T: PartialEq>()
    requires
        obeys_eq::<T>(),
    ensures
        #[trigger] obeys_eq::<Option<T>>(),
{
    reveal(obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_option_obeys_concrete_eq<T: PartialEq>()
    requires
        obeys_concrete_eq::<T>(),
    ensures
        #[trigger] obeys_concrete_eq::<Option<T>>(),
{
    reveal(obeys_concrete_eq);
}

pub broadcast proof fn lemma_option_obeys_view_eq<T: PartialEq + View>()
    requires
        obeys_concrete_eq::<T>(),
    ensures
        #[trigger] obeys_view_eq::<Option<T>>(),
{
    reveal(obeys_concrete_eq);
    reveal(obeys_view_eq);
}

pub broadcast proof fn lemma_option_obeys_deep_eq<T: PartialEq + DeepView>()
    requires
        obeys_deep_eq::<T>(),
    ensures
        #[trigger] obeys_deep_eq::<Option<T>>(),
{
    reveal(obeys_deep_eq);
}

pub broadcast group group_laws_eq {
    axiom_structural_obeys_concrete_eq,
    bool_laws::group_laws_eq,
    u8_laws::group_laws_eq,
    i8_laws::group_laws_eq,
    u16_laws::group_laws_eq,
    i16_laws::group_laws_eq,
    u32_laws::group_laws_eq,
    i32_laws::group_laws_eq,
    u64_laws::group_laws_eq,
    i64_laws::group_laws_eq,
    u128_laws::group_laws_eq,
    i128_laws::group_laws_eq,
    usize_laws::group_laws_eq,
    isize_laws::group_laws_eq,
    tuple_1_laws::group_laws_eq,
    tuple_2_laws::group_laws_eq,
    tuple_3_laws::group_laws_eq,
    tuple_4_laws::group_laws_eq,
    tuple_5_laws::group_laws_eq,
    tuple_6_laws::group_laws_eq,
    tuple_7_laws::group_laws_eq,
    tuple_8_laws::group_laws_eq,
    tuple_9_laws::group_laws_eq,
    tuple_10_laws::group_laws_eq,
    tuple_11_laws::group_laws_eq,
    tuple_12_laws::group_laws_eq,
    lemma_ref_obeys_eq_spec,
    lemma_ref_obeys_concrete_eq,
    lemma_ref_obeys_view_eq,
    lemma_ref_obeys_deep_eq,
    lemma_option_obeys_eq_spec,
    lemma_option_obeys_concrete_eq,
    lemma_option_obeys_view_eq,
    lemma_option_obeys_deep_eq,
}

} // verus!
