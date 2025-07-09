#![feature(rustc_attrs)]
#![allow(unused_imports)]

use super::prelude::*;
use super::std_specs::core::PartialEqSpec;
use super::view::*;

verus! {

#[verifier::opaque]
pub open spec fn obeys_eq_spec_properties<T: PartialEqSpec>() -> bool {
    &&& forall|x: T, y: T| #[trigger] x.eq_spec(&y) <==> y.eq_spec(&x)
    &&& forall|x: T, y: T, z: T|
        x.eq_spec(&y) && #[trigger] y.eq_spec(&z) ==> #[trigger] x.eq_spec(&z)
}

pub open spec fn obeys_eq_spec<T: PartialEqSpec>() -> bool {
    &&& T::obeys_eq_spec()
    &&& obeys_eq_spec_properties::<T>()
}

#[verifier::opaque]
pub open spec fn obeys_concrete_eq<T: PartialEqSpec>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x == y
}

#[verifier::opaque]
pub open spec fn obeys_view_eq<T: PartialEqSpec + View>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x@ == y@
}

#[verifier::opaque]
pub open spec fn obeys_deep_eq<T: PartialEqSpec + DeepView>() -> bool {
    &&& T::obeys_eq_spec()
    &&& forall|x: T, y: T| x.eq_spec(&y) <==> x.deep_view() == y.deep_view()
}

pub broadcast proof fn axiom_structural_obeys_concrete_eq<T: PartialEqSpec + Structural>()
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
                    #[trigger] obeys_eq_spec::<$n>(),
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

pub broadcast proof fn lemma_option_obeys_eq_spec<T: PartialEqSpec>()
    requires
        obeys_eq_spec::<T>(),
    ensures
        #[trigger] obeys_eq_spec::<Option<T>>(),
{
    reveal(obeys_eq_spec_properties);
}

pub broadcast proof fn lemma_option_obeys_concrete_eq<T: PartialEqSpec>()
    requires
        obeys_concrete_eq::<T>(),
    ensures
        #[trigger] obeys_concrete_eq::<Option<T>>(),
{
    reveal(obeys_concrete_eq);
}

pub broadcast proof fn lemma_option_obeys_view_eq<T: PartialEqSpec + View>()
    requires
        obeys_concrete_eq::<T>(),
    ensures
        #[trigger] obeys_view_eq::<Option<T>>(),
{
    reveal(obeys_concrete_eq);
    reveal(obeys_view_eq);
}

pub broadcast proof fn lemma_option_obeys_deep_eq<T: PartialEqSpec + DeepView>()
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
    lemma_option_obeys_eq_spec,
    lemma_option_obeys_concrete_eq,
    lemma_option_obeys_view_eq,
    lemma_option_obeys_deep_eq,
}

} // verus!
