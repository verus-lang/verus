use super::super::prelude::*;
use core::marker::PointeeSized;

use verus as verus_;

verus_! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(DefaultSpec via DefaultSpecImpl)]
pub trait ExDefault: Sized {
    type ExternalTraitSpecificationFor: core::default::Default;

    spec fn obeys_default_spec() -> bool;

    spec fn default_spec() -> Self;

    fn default() -> (r: Self)
        ensures
            Self::obeys_default_spec() ==> r == Self::default_spec(),
    ;
}

} // verus!

macro_rules! impl_default_spec {
    ($t:ty, $default_value:expr) => {
        verus_! {
            pub assume_specification [ <$t as core::default::Default>::default ]() -> (r: $t);

            impl DefaultSpecImpl for $t {
                open spec fn obeys_default_spec() -> bool {
                    true
                }

                open spec fn default_spec() -> Self {
                    $default_value
                }
            }
        }
    };
}

impl_default_spec!(bool, false);
impl_default_spec!(char, '\0');
impl_default_spec!(f32, 0.0f32);
impl_default_spec!(f64, 0.0f64);
impl_default_spec!(i8, 0i8);
impl_default_spec!(i16, 0i16);
impl_default_spec!(i32, 0i32);
impl_default_spec!(i64, 0i64);
impl_default_spec!(i128, 0i128);
impl_default_spec!(isize, 0isize);
impl_default_spec!(u8, 0u8);
impl_default_spec!(u16, 0u16);
impl_default_spec!(u32, 0u32);
impl_default_spec!(u64, 0u64);
impl_default_spec!(u128, 0u128);
impl_default_spec!((), ());
impl_default_spec!(usize, 0usize);

// manually implementation for Option<T>, &str, PhantomData<T>, (U, T), (V, U, T)
verus! {

pub assume_specification<T>[ <Option<T> as core::default::Default>::default ]() -> (r: Option<T>)
;

impl<T> DefaultSpecImpl for Option<T> {
    open spec fn obeys_default_spec() -> bool {
        true
    }

    open spec fn default_spec() -> Self {
        None
    }
}

pub assume_specification<'a>[ <&'a str as core::default::Default>::default ]() -> (r: &'a str)
;

impl<'a> DefaultSpecImpl for &'a str {
    open spec fn obeys_default_spec() -> bool {
        true
    }

    open spec fn default_spec() -> Self {
        ""
    }
}

pub assume_specification<T: PointeeSized>[ <core::marker::PhantomData<
    T,
> as core::default::Default>::default ]() -> (r: core::marker::PhantomData<T>)
;

impl<T: PointeeSized> DefaultSpecImpl for core::marker::PhantomData<T> {
    open spec fn obeys_default_spec() -> bool {
        true
    }

    open spec fn default_spec() -> Self {
        core::marker::PhantomData
    }
}

pub assume_specification<U: core::default::Default, T: core::default::Default>[ <(
    U,
    T,
) as core::default::Default>::default ]() -> (r: (U, T))
    ensures
        call_ensures(U::default, (), r.0),
        call_ensures(T::default, (), r.1),
;

impl<U, T> DefaultSpecImpl for (U, T)
where
    U: core::default::Default,
    T: core::default::Default,
{
    open spec fn obeys_default_spec() -> bool {
        U::obeys_default_spec() && T::obeys_default_spec()
    }

    open spec fn default_spec() -> Self {
        (U::default_spec(), T::default_spec())
    }
}

pub assume_specification<
    V: core::default::Default,
    U: core::default::Default,
    T: core::default::Default,
>[ <(V, U, T) as core::default::Default>::default ]() -> (r: (V, U, T))
    ensures
        call_ensures(V::default, (), r.0),
        call_ensures(U::default, (), r.1),
        call_ensures(T::default, (), r.2),
;

impl<V, U, T> DefaultSpecImpl for (V, U, T)
where
    V: core::default::Default,
    U: core::default::Default,
    T: core::default::Default,
{
    open spec fn obeys_default_spec() -> bool {
        V::obeys_default_spec() && U::obeys_default_spec() && T::obeys_default_spec()
    }

    open spec fn default_spec() -> Self {
        (V::default_spec(), U::default_spec(), T::default_spec())
    }
}

} // verus!
