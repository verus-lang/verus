#![allow(unused_imports)]
use super::super::prelude::*;

use core::convert::{From, Into, TryFrom, TryInto};

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FromSpec via FromSpecImpl)]
pub trait ExFrom<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::From<T>;

    spec fn obeys_from_spec() -> bool;

    spec fn from_spec(v: T) -> Self;

    fn from(v: T) -> (ret: Self)
        ensures
            Self::obeys_from_spec() ==> ret == Self::from_spec(v),
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IntoSpec via IntoSpecImpl)]
pub trait ExInto<T>: Sized {
    type ExternalTraitSpecificationFor: core::convert::Into<T>;

    spec fn obeys_into_spec() -> bool;

    spec fn into_spec(self) -> T;

    fn into(self) -> (ret: T)
        ensures
            Self::obeys_into_spec() ==> ret == Self::into_spec(self),
    ;
}

impl<T, U: From<T>> IntoSpecImpl<U> for T {
    open spec fn obeys_into_spec() -> bool {
        <U as FromSpec<Self>>::obeys_from_spec()
    }

    open spec fn into_spec(self) -> U {
        U::from_spec(self)
    }
}

pub assume_specification<T, U: From<T>>[ <T as Into<U>>::into ](a: T) -> (ret: U)
    ensures
        call_ensures(U::from, (a,), ret),
;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExTryFromIntError(core::num::TryFromIntError);

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TryFromSpec via TryFromSpecImpl)]
pub trait ExTryFrom<T>: Sized {
    type ExternalTraitSpecificationFor: TryFrom<T>;

    type Error;

    spec fn obeys_try_from_spec() -> bool;

    spec fn try_from_spec(v: T) -> Result<Self, Self::Error>;

    fn try_from(v: T) -> (ret: Result<Self, Self::Error>)
        ensures
            Self::obeys_try_from_spec() ==> ret == Self::try_from_spec(v),
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(TryIntoSpec via TryIntoSpecImpl)]
pub trait ExTryInto<T>: Sized {
    type ExternalTraitSpecificationFor: TryInto<T>;

    type Error;

    spec fn obeys_try_into_spec() -> bool;

    spec fn try_into_spec(self) -> Result<T, Self::Error>;

    fn try_into(self) -> (ret: Result<T, Self::Error>)
        ensures
            Self::obeys_try_into_spec() ==> ret == Self::try_into_spec(self),
    ;
}

impl<T, U: TryFrom<T>> TryIntoSpecImpl<U> for T {
    open spec fn obeys_try_into_spec() -> bool {
        <U as TryFromSpec<Self>>::obeys_try_from_spec()
    }

    open spec fn try_into_spec(self) -> Result<U, U::Error> {
        <U as TryFromSpec<Self>>::try_from_spec(self)
    }
}

pub assume_specification<T, U: TryFrom<T>>[ <T as TryInto<U>>::try_into ](a: T) -> (ret: Result<
    U,
    U::Error,
>)
    ensures
        call_ensures(U::try_from, (a,), ret),
;

pub assume_specification<T, U: Into<T>>[ <T as TryFrom<U>>::try_from ](a: U) -> (ret: Result<
    T,
    <T as TryFrom<U>>::Error,
>)
    ensures
        ret.is_ok(),
        call_ensures(U::into, (a,), ret.unwrap()),
;

} // verus!
macro_rules! impl_from_spec {
    ($from: ty => [$($to: ty)*]) => {
        verus!{
        $(
        pub assume_specification[ <$to as core::convert::From<$from>>::from ](a: $from) -> (ret: $to);

        impl FromSpecImpl<$from> for $to {
            open spec fn obeys_from_spec() -> bool {
                true
            }

            open spec fn from_spec(v: $from) -> $to {
                v as $to
            }
        }
        )*
        }
    };
}

impl_from_spec! {u8 => [u16 u32 u64 usize u128]}
impl_from_spec! {u16 => [u32 u64 usize u128]}
impl_from_spec! {u32 => [u64 u128]}
impl_from_spec! {u64 => [u128]}

macro_rules! impl_int_try_from_spec {
    ($from:ty => [$($to:ty)*]) => {
        verus!{
        $(
        pub assume_specification[ <$to as TryFrom<$from>>::try_from ](a: $from) -> (ret: Result<$to, <$to as TryFrom<$from>>::Error>);

        impl TryFromSpecImpl<$from> for $to {
            open spec fn obeys_try_from_spec() -> bool {
                true
            }

            open spec fn try_from_spec(v: $from) -> Result<Self, Self::Error> {
                if Self::MIN <= v <= Self::MAX {
                    Ok(v as $to)
                } else {
                    Err(arbitrary())
                }
            }
        }
        )*
        }
    };
}

impl_int_try_from_spec! { u16 => [u8 i8] }
impl_int_try_from_spec! { u32 => [u8 u16 i8 i16 usize isize] }
impl_int_try_from_spec! { u64 => [u8 u16 u32 i8 i16 i32 usize isize] }
impl_int_try_from_spec! { u128 => [u8 u16 u32 u64 i8 i16 i32 i64 usize isize] }
impl_int_try_from_spec! { usize => [u8 u16 u32 u64 u128 i8 i16 i32 i64] }
