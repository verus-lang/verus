//! This module contains [`Multiset`]-specific method implementations.

use crate::prelude::*;
use crate::contrib::exec_spec::*;

verus! {

//
// Trait definitions for methods
//

/// Spec for executable version of [`Multiset::count`].
// todo(nneamtu): this spec only works for primitive T right now
pub trait ExecSpecCount<T>: Sized + DeepView {
    fn exec_count(self, value: T) -> usize;
}

//
// Implementations for ExecMultiset
//

impl<'a, T: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecCount<T> for &'a ExecMultiset<T> {
    #[inline(always)]
    #[verifier::external_body]
    fn exec_count(self, value: T) -> (res: usize)
        ensures
            res == self.deep_view().count(value.deep_view()),
    {
        match self.m.get(&value) {
            Some(v) => v.deep_clone(),
            None => 0
        }
    }
}

}