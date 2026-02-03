#![allow(unused_imports)]
use super::super::prelude::*;

#[cfg(feature = "alloc")]
use alloc::borrow::Borrow;
#[cfg(feature = "alloc")]
use alloc::borrow::Cow;
#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;

verus! {

#[cfg(feature = "alloc")]
#[verifier::external_trait_specification]
pub(crate) trait ExToOwned {
    type ExternalTraitSpecificationFor: ToOwned;

    type Owned: Borrow<Self>;
}

#[cfg(feature = "alloc")]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(B)]
pub struct ExCow<'a, B: 'a + ?Sized + ToOwned>(Cow<'a, B>);

// We are using `T: Clone` as a more restrictive bound than what's in std (where
// T: ToOwned), since ToOwned::Owned may be a different type than `T`.
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

// We are using `T: Clone` as a more restrictive bound than what's in std (where
// T: ToOwned), since ToOwned::Owned may be a different type than `T`.
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

// Note: this is not covered by the blanket impl for `T: View + Clone`, since `str` does not implement clone.
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
