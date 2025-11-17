#![allow(unused_imports)]
use super::super::prelude::*;

use core::convert::{From, Into};

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

pub assume_specification<T, U: From<T>>[ T::into ](a: T) -> (ret: U)
    ensures
        call_ensures(U::from, (a,), ret),
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
