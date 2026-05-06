use super::super::prelude::*;
use core::marker::PointeeSized;

verus! {

#[verifier::external_trait_specification]
pub trait ExDefault: Sized {
    type ExternalTraitSpecificationFor: core::default::Default;

    fn default() -> (r: Self);
}

} // verus!
macro_rules! assume_default_value {
    ($t:ty, $default_value:expr) => {
        verus! {
            pub assume_specification [ <$t as core::default::Default>::default ]() -> (r: $t)
                ensures
                    r == $default_value,
            ;
        }
    };
}

assume_default_value!(bool, false);
assume_default_value!(char, '\0');
assume_default_value!(f32, 0.0f32);
assume_default_value!(f64, 0.0f64);
assume_default_value!(i8, 0i8);
assume_default_value!(i16, 0i16);
assume_default_value!(i32, 0i32);
assume_default_value!(i64, 0i64);
assume_default_value!(i128, 0i128);
assume_default_value!(isize, 0isize);
assume_default_value!(u8, 0u8);
assume_default_value!(u16, 0u16);
assume_default_value!(u32, 0u32);
assume_default_value!(u64, 0u64);
assume_default_value!(u128, 0u128);
assume_default_value!((), ());
assume_default_value!(usize, 0usize);

// manually implementation for Option<T>, &str, PhantomData<T>, (U, T), (V, U, T)
verus! {

pub assume_specification<T>[ <Option<T> as core::default::Default>::default ]() -> (r: Option<T>)
    ensures
        r == Option::<T>::None,
;

pub assume_specification<'a>[ <&'a str as core::default::Default>::default ]() -> (r: &'a str)
    ensures
        r == "",
;

pub assume_specification<T: PointeeSized>[ <core::marker::PhantomData<
    T,
> as core::default::Default>::default ]() -> (r: core::marker::PhantomData<T>)
    ensures
        r == core::marker::PhantomData::<T>,
;

pub assume_specification<U: core::default::Default, T: core::default::Default>[ <(
    U,
    T,
) as core::default::Default>::default ]() -> (r: (U, T))
    ensures
        call_ensures(U::default, (), r.0),
        call_ensures(T::default, (), r.1),
;

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

} // verus!
