#![allow(unused_imports)]
use super::super::prelude::*;

use core::borrow::Borrow;
use std::borrow::Cow;
use std::borrow::Cow::Borrowed;
use std::borrow::Cow::Owned;
use std::borrow::ToOwned;

verus! {

#[verifier::external_trait_specification]
pub(crate) trait ExToOwned {
    type ExternalTraitSpecificationFor: ToOwned;

    type Owned: Borrow<Self>;
}

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(B)]
pub struct ExCow<'a, B: 'a + ?Sized + ToOwned>(Cow<'a, B>);

#[cfg(feature = "alloc")]
impl<'a, T: View + Clone> View for Cow<'a, T> {
    type V = T::V;

    open spec fn view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed@,
            Cow::Owned(owned) => owned@,
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: DeepView + Clone> DeepView for Cow<'a, T> {
    type V = T::V;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed.deep_view(),
            Cow::Owned(owned) => owned.deep_view(),
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a> View for Cow<'a, str> {
    type V = Seq<char>;

    open spec fn view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed@,
            Cow::Owned(owned) => owned@,
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a> DeepView for Cow<'a, str> {
    type V = Seq<char>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed.deep_view(),
            Cow::Owned(owned) => owned.deep_view(),
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: View + Clone> View for Cow<'a, [T]> {
    type V = Seq<T>;

    open spec fn view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed@,
            Cow::Owned(owned) => owned@,
        }
    }
}

#[cfg(feature = "alloc")]
impl<'a, T: DeepView + Clone> DeepView for Cow<'a, [T]> {
    type V = Seq<T::V>;

    open spec fn deep_view(&self) -> Self::V {
        match self {
            Cow::Borrowed(borrowed) => borrowed.deep_view(),
            Cow::Owned(owned) => owned.deep_view(),
        }
    }
}

} // verus!
