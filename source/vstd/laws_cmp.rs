#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::laws_eq::*;
use super::prelude::*;
use core::cmp::Ordering;

verus! {

/// WARNING: partial_cmp_result is experimental and is likely to change
#[verifier::opaque]
pub open spec fn partial_cmp_result<T: PartialOrd>(x: T, y: T) -> Option<Ordering> {
    choose|o: Option<Ordering>| call_ensures(T::partial_cmp, (&x, &y), o)
}

/// WARNING: cmp_result is experimental and is likely to change
#[verifier::opaque]
pub open spec fn cmp_result<T: Ord>(x: T, y: T) -> Ordering {
    choose|o: Ordering| call_ensures(T::cmp, (&x, &y), o)
}

#[verifier::opaque]
pub open spec fn obeys_partial_cmp_spec_properties<T: PartialOrd>() -> bool {
    &&& forall|x: T, y: T| #[trigger]
        partial_cmp_result(x, y) == Some(Ordering::Equal) <==> eq_result(y, x)
    &&& forall|x: T, y: T| #[trigger]
        partial_cmp_result(x, y) == Some(Ordering::Less) <==> partial_cmp_result(y, x) == Some(
            Ordering::Greater,
        )
    &&& forall|x: T, y: T, z: T|
        partial_cmp_result(x, y) == Some(Ordering::Less) && #[trigger] partial_cmp_result(y, z)
            == Some(Ordering::Less) ==> #[trigger] partial_cmp_result(x, z) == Some(Ordering::Less)
    &&& forall|x: T, y: T, z: T|
        partial_cmp_result(x, y) == Some(Ordering::Greater) && #[trigger] partial_cmp_result(y, z)
            == Some(Ordering::Greater) ==> #[trigger] partial_cmp_result(x, z) == Some(
            Ordering::Greater,
        )
    &&& obeys_eq_spec_properties::<T>()
}

#[verifier::opaque]
pub open spec fn obeys_cmp_partial_ord<T: PartialOrd>() -> bool {
    &&& forall|x: T, y: T|
        call_ensures(T::partial_cmp, (&x, &y), #[trigger] partial_cmp_result(x, y))
    &&& forall|x: T, y: T, o: Option<Ordering>|
        call_ensures(T::partial_cmp, (&x, &y), o) ==> o == partial_cmp_result(x, y)
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::lt, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) == Some(
            Ordering::Less,
        ))
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::gt, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) == Some(
            Ordering::Greater,
        ))
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::le, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) matches Some(
            Ordering::Less
            | Ordering::Equal,
        ))
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::ge, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) matches Some(
            Ordering::Greater
            | Ordering::Equal,
        ))
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::eq, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) == Some(
            Ordering::Equal,
        ))
    &&& forall|x: T, y: T, b: bool|
        call_ensures(T::ne, (&x, &y), b) ==> (b <==> partial_cmp_result(x, y) != Some(
            Ordering::Equal,
        ))
}

#[verifier::opaque]
pub open spec fn obeys_cmp_ord<T: Ord>() -> bool {
    &&& forall|x: T, y: T| call_ensures(T::cmp, (&x, &y), #[trigger] cmp_result(x, y))
    &&& forall|x: T, y: T, o: Ordering| call_ensures(T::cmp, (&x, &y), o) ==> o == cmp_result(x, y)
    &&& forall|x: T, y: T| #[trigger] partial_cmp_result(x, y).is_some()
    &&& forall|x: T, y: T|
        #![trigger partial_cmp_result(x, y)]
        #![trigger cmp_result(x, y)]
        partial_cmp_result(x, y) == Some(cmp_result(x, y))
}

pub open spec fn obeys_cmp_spec<T: Ord>() -> bool {
    &&& obeys_eq_spec::<T>()
    &&& obeys_cmp_partial_ord::<T>()
    &&& obeys_cmp_ord::<T>()
    &&& obeys_partial_cmp_spec_properties::<T>()
}

pub proof fn lemma_ensures_partial_cmp<T: PartialOrd>(witness: spec_fn(T, T) -> Option<Ordering>)
    requires
        forall|x: T, y: T| call_ensures(T::partial_cmp, (&x, &y), #[trigger] witness(x, y)),
    ensures
        forall|x: T, y: T|
            call_ensures(T::partial_cmp, (&x, &y), #[trigger] partial_cmp_result(x, y)),
{
    reveal(partial_cmp_result);
    assert forall|x: T, y: T|
        call_ensures(T::partial_cmp, (&x, &y), #[trigger] partial_cmp_result(x, y)) by {
        assert(call_ensures(T::partial_cmp, (&x, &y), witness(x, y)));
    }
}

pub proof fn lemma_ensures_cmp<T: Ord>(witness: spec_fn(T, T) -> Ordering)
    requires
        forall|x: T, y: T| call_ensures(T::partial_cmp, (&x, &y), Some(#[trigger] witness(x, y))),
        forall|x: T, y: T| call_ensures(T::cmp, (&x, &y), #[trigger] witness(x, y)),
    ensures
        forall|x: T, y: T|
            call_ensures(T::partial_cmp, (&x, &y), #[trigger] partial_cmp_result(x, y)),
        forall|x: T, y: T| call_ensures(T::cmp, (&x, &y), #[trigger] cmp_result(x, y)),
{
    lemma_ensures_partial_cmp(|x: T, y: T| Some(witness(x, y)));
    reveal(cmp_result);
    assert forall|x: T, y: T| call_ensures(T::cmp, (&x, &y), #[trigger] cmp_result(x, y)) by {
        assert(call_ensures(T::cmp, (&x, &y), witness(x, y)));
    }
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
                reveal(obeys_eq_partial_eq);
                reveal(obeys_partial_cmp_spec_properties);
                reveal(obeys_cmp_partial_ord);
                reveal(obeys_cmp_ord);
                assert(obeys_eq_spec::<$n>());
                lemma_ensures_cmp(
                    |x: $n, y: $n| {
                        if x < y { Ordering::Less }
                        else if x > y { Ordering::Greater }
                        else { Ordering::Equal }
                    }
                );
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

pub broadcast proof fn lemma_option_obeys_cmp_spec<T: Ord>()
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
        lemma_ensures_cmp(
            |x: Option<T>, y: Option<T>|
                {
                    match (x, y) {
                        (None, None) => Ordering::Equal,
                        (None, Some(_)) => Ordering::Less,
                        (Some(_), None) => Ordering::Greater,
                        (Some(xx), Some(yy)) => cmp_result(xx, yy),
                    }
                },
        );
    }

    assert(obeys_partial_cmp_spec_properties::<Option<T>>()) by {
        reveal(obeys_eq_partial_eq);
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
