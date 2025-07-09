#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::laws_eq::*;
use super::prelude::*;
use super::std_specs::core::{OrdSpec, PartialEqSpec, PartialOrdSpec};
use core::cmp::Ordering;

verus! {

#[verifier::opaque]
pub open spec fn obeys_partial_cmp_spec_properties<T: PartialOrdSpec>() -> bool {
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
pub open spec fn obeys_cmp_partial_ord<T: PartialOrdSpec>() -> bool {
    &&& T::obeys_eq_spec()
    &&& T::obeys_partial_cmp_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x.partial_cmp_spec(&y) == Some(Ordering::Equal)
}

#[verifier::opaque]
pub open spec fn obeys_cmp_ord<T: OrdSpec>() -> bool {
    &&& T::obeys_cmp_spec()
    &&& forall|x: T, y: T|
        #![trigger x.partial_cmp_spec(&y)]
        #![trigger x.cmp_spec(&y)]
        x.partial_cmp_spec(&y) == Some(x.cmp_spec(&y))
}

pub open spec fn obeys_cmp_spec<T: OrdSpec>() -> bool {
    &&& obeys_eq_spec::<T>()
    &&& obeys_cmp_partial_ord::<T>()
    &&& obeys_cmp_ord::<T>()
    &&& obeys_partial_cmp_spec_properties::<T>()
}

macro_rules! num_laws_cmp {
    ($n: ty, $modname:ident) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_cmp_spec()
                ensures
                    #[trigger] obeys_cmp_spec::<$n>(),
            {
                broadcast use group_laws_eq;
                reveal(obeys_eq_spec_properties);
                reveal(obeys_partial_cmp_spec_properties);
                reveal(obeys_cmp_partial_ord);
                reveal(obeys_cmp_ord);
                assert(obeys_eq_spec::<$n>());
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

pub broadcast proof fn lemma_option_obeys_cmp_spec<T: PartialEqSpec + PartialOrdSpec + OrdSpec>()
    requires
        obeys_cmp_spec::<T>(),
    ensures
        #[trigger] obeys_cmp_spec::<Option<T>>(),
{
    broadcast use lemma_option_obeys_eq_spec;

    assert(obeys_eq_spec::<Option<T>>());

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
    lemma_option_obeys_cmp_spec,
}

} // verus!
