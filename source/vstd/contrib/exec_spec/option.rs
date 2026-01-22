use crate::prelude::*;
use crate::contrib::exec_spec::*;
use std::collections::{HashMap, HashSet};

verus! {

/// Impls for shared traits

impl<'a, T: Sized + DeepView> ToRef<&'a Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a Option<T> {
        self
    }
}

impl<'a, T: DeepView + DeepViewClone> ToOwned<Option<T>> for &'a Option<T> {
    #[inline(always)]
    fn get_owned(self) -> Option<T> {
        self.deep_clone()
    }
}

impl<T: DeepViewClone> DeepViewClone for Option<T> {
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        match self {
            Some(t) => Some(t.deep_clone()),
            None => None,
        }
    }
}

impl<'a, T: DeepView> ExecSpecEq<'a> for &'a Option<T> where &'a T: ExecSpecEq<'a, Other = &'a T> {
    type Other = &'a Option<T>;

    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        match (this, other) {
            (Some(t1), Some(t2)) => <&'a T>::exec_eq(t1, t2),
            (None, None) => true,
            _ => false,
        }
    }
}

/// Traits for Option methods

/// Spec for executable version of [`Option::unwrap`].
pub trait ExecSpecOptionUnwrap<'a>: Sized + DeepView {
    type Elem: DeepView + DeepViewClone;

    spec fn is_some_spec(&self) -> bool;

    fn exec_unwrap(self) -> Self::Elem
        requires
            self.is_some_spec()
    ;
}


/// Impls for Option methods

impl<'a,T> ExecSpecOptionUnwrap<'a> for &'a Option<T> where T: DeepView + DeepViewClone {
    type Elem = T;

    closed spec fn is_some_spec(&self) -> bool {
        self.is_some()
    }

    #[inline(always)]
    fn exec_unwrap(self) -> (res: Self::Elem)
        ensures
            res.deep_view() == self.deep_view()->0,
    {
        self.deep_clone().unwrap()
    }
}


}