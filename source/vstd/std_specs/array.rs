use super::super::prelude::*;

verus! {

// array == array
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U; N]>>::eq ](
    left: &[T; N],
    right: &[U; N],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < N ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(&self@[i], &other@[i])
    }
}

// slice ref == array
pub assume_specification<'a, T: PartialEq<U>, U, const N: usize>[ <&'a [T] as PartialEq<
    [U; N],
>>::eq ](left: &&'a [T], right: &[U; N]) -> bool
;

impl<'a, T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for &'a [T] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        &&& (*self)@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < (*self)@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &(*self)@[i],
                &other@[i],
            )
    }
}

// array == slice ref
pub assume_specification<'a, T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<&[U]>>::eq ](
    left: &[T; N],
    right: &&[U],
) -> bool
;

impl<'a, T, U, const N: usize> super::cmp::PartialEqSpecImpl<&'a [U]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &&'a [U]) -> bool {
        &&& self@.len() == (*other)@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &(*other)@[i],
            )
    }
}

// slice == array
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T] as PartialEq<[U; N]>>::eq ](
    left: &[T],
    right: &[U; N],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U; N]> for [T] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U; N]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &other@[i],
            )
    }
}

// array == slice
pub assume_specification<T: PartialEq<U>, U, const N: usize>[ <[T; N] as PartialEq<[U]>>::eq ](
    left: &[T; N],
    right: &[U],
) -> bool
;

impl<T, U, const N: usize> super::cmp::PartialEqSpecImpl<[U]> for [T; N] where
    T: PartialEq<U> + super::cmp::PartialEqSpec<U>,
 {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(
                &self@[i],
                &other@[i],
            )
    }
}

} // verus!
