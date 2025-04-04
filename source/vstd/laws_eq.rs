#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use super::view::*;

verus! {

/// WARNING: eq_result is experimental and is likely to change
#[verifier::opaque]
pub open spec fn eq_result<T: PartialEq>(x: T, y: T) -> bool {
    choose|o: bool| call_ensures(T::eq, (&x, &y), o)
}

#[verifier::opaque]
pub open spec fn obeys_eq_spec_properties<T: PartialEq>() -> bool {
    &&& forall|x: T, y: T| #[trigger] eq_result(x, y) <==> eq_result(y, x)
    &&& forall|x: T, y: T, z: T|
        eq_result(x, y) && #[trigger] eq_result(y, z) ==> #[trigger] eq_result(x, z)
}

#[verifier::opaque]
pub open spec fn obeys_eq_partial_eq<T: PartialEq>() -> bool {
    &&& forall|x: T, y: T| call_ensures(T::eq, (&x, &y), #[trigger] eq_result(x, y))
    &&& forall|x: T, y: T, b: bool| call_ensures(T::eq, (&x, &y), b) ==> (b <==> eq_result(x, y))
    &&& forall|x: T, y: T, b: bool| call_ensures(T::ne, (&x, &y), b) ==> (b <==> !eq_result(x, y))
}

pub open spec fn obeys_eq_spec<T: PartialEq>() -> bool {
    &&& obeys_eq_spec_properties::<T>()
    &&& obeys_eq_partial_eq::<T>()
}

#[verifier::opaque]
pub open spec fn obeys_concrete_eq<T: PartialEq>() -> bool {
    &&& forall|x: T, y: T, b: bool| call_ensures(T::eq, (&x, &y), b) ==> (b <==> x == y)
}

#[verifier::opaque]
pub open spec fn obeys_view_eq<T: PartialEq + View>() -> bool {
    forall|x: T, y: T, b: bool| call_ensures(T::eq, (&x, &y), b) ==> (b <==> x@ == y@)
}

#[verifier::opaque]
pub open spec fn obeys_deep_eq<T: PartialEq + DeepView>() -> bool {
    forall|x: T, y: T, b: bool|
        call_ensures(T::eq, (&x, &y), b) ==> (b <==> x.deep_view() == y.deep_view())
}

pub proof fn lemma_ensures_partial_eq<T: PartialEq>(witness: spec_fn(T, T) -> bool)
    requires
        forall|x: T, y: T| call_ensures(T::eq, (&x, &y), #[trigger] witness(x, y)),
    ensures
        forall|x: T, y: T| call_ensures(T::eq, (&x, &y), #[trigger] eq_result(x, y)),
{
    reveal(eq_result);
    assert forall|x: T, y: T| call_ensures(T::eq, (&x, &y), #[trigger] eq_result(x, y)) by {
        assert(call_ensures(T::eq, (&x, &y), witness(x, y)));
    }
}

pub broadcast proof fn axiom_structural_obeys_eq_spec<T: PartialEq + Structural>()
    ensures
        #[trigger] obeys_eq_spec::<T>(),
{
    admit();
}

pub broadcast proof fn axiom_structural_obeys_concrete_eq<T: PartialEq + Structural>()
    ensures
        #[trigger] obeys_concrete_eq::<T>(),
{
    admit();
}

macro_rules! primitive_laws_eq {
    ($n: ty, $modname:ident) => {
        verus! {
        mod $modname {
            use super::*;

            pub broadcast proof fn lemma_obeys_eq_spec()
                ensures
                    #[trigger] obeys_eq_spec::<$n>(),
            {
                reveal(obeys_eq_spec_properties);
                reveal(obeys_eq_partial_eq);
                lemma_ensures_partial_eq(|x: $n, y: $n| x == y);
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

pub broadcast proof fn lemma_option_obeys_eq_spec<T: PartialEq>()
    requires
        obeys_eq_spec::<T>(),
    ensures
        #[trigger] obeys_eq_spec::<Option<T>>(),
{
    reveal(obeys_eq_spec_properties);
    reveal(obeys_eq_partial_eq);
    lemma_ensures_partial_eq(
        |x: Option<T>, y: Option<T>|
            {
                match (x, y) {
                    (None, None) => true,
                    (Some(xx), Some(yy)) => eq_result(xx, yy),
                    _ => false,
                }
            },
    );
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
    axiom_structural_obeys_eq_spec,
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
    lemma_option_obeys_eq_spec,
    lemma_option_obeys_concrete_eq,
    lemma_option_obeys_view_eq,
    lemma_option_obeys_deep_eq,
}

} // verus!
