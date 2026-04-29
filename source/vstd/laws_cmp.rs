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
                    $($T: Ord + PartialEq + PartialEqSpec + OrdSpec,)+
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

tuple_cmp_impl!(tuple_3_laws, V U T);

tuple_cmp_impl!(tuple_4_laws, W V U T);

tuple_cmp_impl!(tuple_5_laws, X W V U T);

tuple_cmp_impl!(tuple_6_laws, Y X W V U T);

/* These exaust a lot of resource limits
tuple_cmp_impl!(tuple_7_laws, Z Y X W V U T);
tuple_cmp_impl!(tuple_8_laws, A Z Y X W V U T);
tuple_cmp_impl!(tuple_9_laws, B A Z Y X W V U T);
tuple_cmp_impl!(tuple_10_laws, C B A Z Y X W V U T);
tuple_cmp_impl!(tuple_11_laws, D C B A Z Y X W V U T);
tuple_cmp_impl!(tuple_12_laws, E D C B A Z Y X W V U T);
*/

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
    tuple_6_laws::lemma_obeys_cmp_spec,/* These exhaust resource limits
    tuple_7_laws::lemma_obeys_cmp_spec,
    tuple_8_laws::lemma_obeys_cmp_spec,
    tuple_9_laws::lemma_obeys_cmp_spec,
    tuple_10_laws::lemma_obeys_cmp_spec,
    tuple_11_laws::lemma_obeys_cmp_spec,
    tuple_12_laws::lemma_obeys_cmp_spec,
    */
}

} // verus!
