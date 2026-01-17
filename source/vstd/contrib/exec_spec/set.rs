//! This module contains [`Set`]-specific method implementations.

use crate::prelude::*;
use crate::contrib::exec_spec::*;
use std::collections::HashSet;

verus! {

/// Impls for shared traits

impl<'a, K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ToRef<&'a HashSet<K>> for &'a HashSet<K> {
    #[inline(always)]
    fn get_ref(self) -> &'a HashSet<K> {
        &self
    }
}

impl<'a, K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ToOwned<HashSet<K>> for &'a HashSet<K> {
    #[verifier::external_body]
    #[inline(always)]
    fn get_owned(self) -> HashSet<K> {
        let mut new_set = HashSet::new();
        for k in self.iter() {
            new_set.insert(k.deep_clone());
        }
        new_set
    }
}

impl<K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> DeepViewClone for HashSet<K> {
    #[verifier::external_body]
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        let mut new_set = HashSet::new();
        for k in self.iter() {
            new_set.insert(k.deep_clone());
        }
        new_set
    }
}

impl<'a, K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecEq<'a> for &'a HashSet<K> 
    where &'a K: ExecSpecEq<'a, Other = &'a K>
{
    type Other = &'a HashSet<K>;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        if this.len() != other.len() {
            return false;
        }
        for k in this.iter() {
            if !other.contains(k) {
                return false;
            }
        }
        true
    }
}

impl<'a, K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecLen for &'a HashSet<K> {
    #[inline(always)]
    #[verifier::external_body]
    fn exec_len(self) -> (res: usize)
        ensures
            res == self.deep_view().len(),
    {
        self.len()
    }
}

/// Traits for Set methods

/// Spec for executable version of [`Set::empty`].
pub trait ExecSpecSetEmpty: Sized {
    fn exec_empty() -> Self;
}

/// Spec for executable version of [`Set::contains`].
pub trait ExecSpecSetContains<'a>: Sized + DeepView {
    type Elem: DeepView;

    fn exec_contains(self, a: Self::Elem) -> bool;
}

/// Spec for executable version of [`Set::insert`].
pub trait ExecSpecSetInsert<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_insert(self, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Set::remove`].
pub trait ExecSpecSetRemove<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Elem: DeepView + DeepViewClone;

    fn exec_remove(self, a: Self::Elem) -> Out;
}

/// Spec for executable version of [`Set::intersect`].
pub trait ExecSpecSetIntersect<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_intersect(self, s2: Self) -> Out;
}

/// Spec for executable version of [`Set::union`].
pub trait ExecSpecSetUnion<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_union(self, s2: Self) -> Out;
}

/// Spec for executable version of [`Set::difference`].
pub trait ExecSpecSetDifference<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_difference(self, s2: Self) -> Out;
}

/// Impls for executable versions of Map methods

impl<K: DeepView + std::hash::Hash + std::cmp::Eq> ExecSpecSetEmpty for HashSet<K> {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_empty() -> (res: Self)
        ensures
            res.deep_view() =~= Set::empty(),
    {
        HashSet::new()
    }
}

impl<'a, K: DeepView + std::hash::Hash + std::cmp::Eq> ExecSpecSetContains<'a> for &'a HashSet<K> {
    type Elem = K;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_contains(self, a: Self::Elem) -> (res: bool)
        ensures
            res == self.deep_view().contains(a.deep_view()),
    {
        self.contains(&a)
    }
}

impl<'a, K> ExecSpecSetInsert<'a, HashSet<K>> for &'a HashSet<K> 
    where K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq
{
    type Elem = K;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_insert(self, a: Self::Elem) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().insert(a.deep_view()),
    {
        let mut m = self.deep_clone();
        let _ = m.insert(a.deep_clone());
        m
    }
}

impl<'a, K> ExecSpecSetRemove<'a, HashSet<K>> for &'a HashSet<K> 
    where K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq
{
    type Elem = K;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_remove(self, a: Self::Elem) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().remove(a.deep_view()),
    {
        let mut m = self.deep_clone();
        let _ = m.remove(&a);
        m
    }
}

impl<'a, K> ExecSpecSetIntersect<'a, HashSet<K>> for &'a HashSet<K> 
    where K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq
{
    #[verifier::external_body]
    #[inline(always)]
    fn exec_intersect(self, s2: Self) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().intersect(s2.deep_view()),
    {
        let mut intersect = HashSet::new();
        for k in self.iter() {
            if s2.contains(k) {
                intersect.insert(k.deep_clone());
            }
        }
        intersect
    }
}

impl<'a, K> ExecSpecSetUnion<'a, HashSet<K>> for &'a HashSet<K> 
    where K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq
{
    #[verifier::external_body]
    #[inline(always)]
    fn exec_union(self, s2: Self) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().union(s2.deep_view()),
    {
        let mut un = self.deep_clone();
        for k in s2.iter() {
            un.insert(k.deep_clone());
        }
        un
    }
}

impl<'a, K> ExecSpecSetDifference<'a, HashSet<K>> for &'a HashSet<K> 
    where K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq
{
    #[verifier::external_body]
    #[inline(always)]
    fn exec_difference(self, s2: Self) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().difference(s2.deep_view()),
    {
        let mut diff = HashSet::new();
        for k in self.iter() {
            if !s2.contains(k) {
                diff.insert(k.deep_clone());
            }
        }
        diff
    }
}
}