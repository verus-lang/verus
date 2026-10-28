#![allow(unused_imports)]
use super::super::prelude::*;

#[cfg(feature = "alloc")]
use alloc::borrow::Borrow;
#[cfg(feature = "alloc")]
use alloc::borrow::Cow;
#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(all(feature = "alloc", not(verus_verify_core)))]
use alloc::string::String;
#[cfg(feature = "alloc")]
use core::alloc::Allocator;

verus! {

#[cfg(feature = "alloc")]
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(BorrowSpec via BorrowSpecImpl)]
pub trait ExBorrow<Borrowed: ?Sized> {
    type ExternalTraitSpecificationFor: Borrow<Borrowed>;

    spec fn obeys_borrow_spec() -> bool;

    spec fn spec_borrow(&self) -> &Borrowed;

    fn borrow(&self) -> (result: &Borrowed)
        ensures
            Self::obeys_borrow_spec() ==> result == self.spec_borrow(),
    ;
}

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

#[cfg(feature = "alloc")]
impl<T: ?Sized> BorrowSpecImpl<T> for T {
    open spec fn obeys_borrow_spec() -> bool {
        true
    }

    open spec fn spec_borrow(&self) -> &T {
        self
    }
}

#[cfg(feature = "alloc")]
pub assume_specification<T: ?Sized>[ <T as Borrow<T>>::borrow ](r: &T) -> (result: &T)
    ensures
        result == r,
;

#[cfg(feature = "alloc")]
impl<T: ?Sized> BorrowSpecImpl<T> for &T {
    open spec fn obeys_borrow_spec() -> bool {
        true
    }

    open spec fn spec_borrow(&self) -> &T {
        *self
    }
}

#[cfg(feature = "alloc")]
pub assume_specification<'b, T: ?Sized, 'a>[ <&'b T as Borrow<T>>::borrow ](
    r: &'a &'b T,
) -> (result: &'a T)
    ensures
        result == *r,
;

#[cfg(feature = "alloc")]
impl<T: ?Sized, A: Allocator> BorrowSpecImpl<T> for Box<T, A> {
    open spec fn obeys_borrow_spec() -> bool {
        true
    }

    open spec fn spec_borrow(&self) -> &T {
        &**self
    }
}

#[cfg(feature = "alloc")]
pub assume_specification<T: ?Sized, A: Allocator>[ <Box<T, A> as Borrow<T>>::borrow ](
    b: &Box<T, A>,
) -> (result: &T)
    ensures
        result == &**b,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
impl BorrowSpecImpl<str> for String {
    open spec fn obeys_borrow_spec() -> bool {
        true
    }

    uninterp spec fn spec_borrow(&self) -> &str;
}

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub broadcast axiom fn axiom_string_borrow(s: &String)
    ensures
        #[trigger] <String as BorrowSpec<str>>::spec_borrow(s)@ == s@,
;

#[cfg(all(feature = "alloc", not(verus_verify_core)))]
pub assume_specification[ <String as Borrow<str>>::borrow ](s: &String) -> (result: &str)
    ensures
        result@ == s@,
;

pub broadcast group group_borrow_axioms {
    #[cfg(all(feature = "alloc", not(verus_verify_core)))]
    axiom_string_borrow,
}

} // verus!
