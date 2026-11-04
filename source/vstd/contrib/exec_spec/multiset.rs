//! This module contains [`Multiset`]-specific method implementations.
use crate::contrib::exec_spec::*;
use crate::prelude::*;
use std::collections::HashMap;

verus! {

// Note: all of the exec translations are currently unverified.
// Some will require axiomatization because their corresponding specs are uninterp.
// They compute with T's Hash/Eq, which agree with T::deep_view() by `T: ObeysDeepEq`.
broadcast use {
    crate::group_vstd_default,
    crate::std_specs::hash::group_hash_axioms,
    crate::std_specs::hash::lemma_hashmap_deepview_dom,
};

/// `Multiset<T>` is compiled to `ExecMultiset<T>`.
#[derive(Eq, Debug)]
pub struct ExecMultiset<T: std::hash::Hash + std::cmp::Eq> {
    pub m: HashMap<T, usize>,
}

/// Compares multiplicities, where an absent element has multiplicity 0 (as in the deep view).
impl<T: std::hash::Hash + std::cmp::Eq> PartialEq for ExecMultiset<T> {
    #[verifier::external_body]
    fn eq(&self, other: &Self) -> bool {
        let count = |m: &HashMap<T, usize>, k: &T| m.get(k).copied().unwrap_or(0);
        self.m.iter().all(|(k, v)| count(&other.m, k) == *v) && other.m.iter().all(
            |(k, v)| count(&self.m, k) == *v,
        )
    }
}

#[cfg(verus_keep_ghost)]
impl<
    T: ObeysDeepEq + std::hash::Hash + std::cmp::Eq,
> crate::std_specs::cmp::PartialEqSpecImpl for ExecMultiset<T> {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Self) -> bool {
        self.deep_view() == other.deep_view()
    }
}

impl<T: ObeysDeepEq + std::hash::Hash + std::cmp::Eq> ObeysDeepEq for ExecMultiset<T> {
    proof fn lemma_obeys_deep_eq() {
        reveal(crate::laws_eq::obeys_deep_eq);
    }
}

/// Implementations for shared traits
/*
trouble implementing this - complains about lifetime of T
impl<T: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq> ExecSpecType for Multiset<T> {
    type ExecOwnedType = ExecMultiset<T>;

    type ExecRefType<'a> = &'a ExecMultiset<T>;
}*/
impl<T: DeepView + std::hash::Hash + std::cmp::Eq> DeepView for ExecMultiset<T> {
    type V = Multiset<<T as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        Multiset::from_map(self.m.deep_view().map_values(|v| v as nat))
    }
}

impl<'a, T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq> ToRef<
    &'a ExecMultiset<T>,
> for &'a ExecMultiset<T> {
    #[inline(always)]
    fn get_ref(self) -> &'a ExecMultiset<T> {
        &self
    }
}

impl<'a, T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq> ToOwned<
    ExecMultiset<T>,
> for &'a ExecMultiset<T> {
    #[verifier::external_body]
    #[inline(always)]
    fn get_owned(self) -> ExecMultiset<T> {
        let mut new_map = HashMap::new();
        for (k, v) in self.m.iter() {
            new_map.insert(k.deep_clone(), v.deep_clone());
        }
        ExecMultiset { m: new_map }
    }
}

impl<
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
> DeepViewClone for ExecMultiset<T> {
    #[verifier::external_body]
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        let mut new_map = HashMap::new();
        for (k, v) in self.m.iter() {
            new_map.insert(k.deep_clone(), v.deep_clone());
        }
        ExecMultiset { m: new_map }
    }
}

impl<
    'a,
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
> ExecSpecLen for &'a ExecMultiset<T> {
    #[inline(always)]
    #[verifier::external_body]
    fn exec_len(self) -> (res: usize)
        ensures
            res == self.deep_view().len(),
    {
        let mut len = 0;
        for (_, v) in self.m.iter() {
            len = len + v;
        }
        len
    }
}

//
// Trait definitions for methods
//
/// Spec for executable version of [`Multiset::count`].
pub trait ExecSpecMultisetCount: Sized + DeepView {
    type Elem;

    fn exec_count(self, value: Self::Elem) -> usize;
}

/// Spec for executable version of [`Multiset::empty`].
pub trait ExecSpecMultisetEmpty: Sized {
    fn exec_empty() -> Self;
}

/// Spec for executable version of [`Multiset::singleton`].
pub trait ExecSpecMultisetSingleton: Sized {
    type Elem;

    fn exec_singleton(v: Self::Elem) -> Self;
}

/// Spec for executable version of [`Multiset::add`].
pub trait ExecSpecMultisetAdd<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_add(self, m2: Self) -> Out;
}

/// Spec for executable version of [`Multiset::sub`].
pub trait ExecSpecMultisetSub<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    fn exec_sub(self, m2: Self) -> Out;
}

//
// Implementations for ExecMultiset
//
impl<
    'a,
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
> ExecSpecMultisetCount for &'a ExecMultiset<T> {
    type Elem = T;

    #[inline(always)]
    #[verifier::external_body]
    fn exec_count(self, value: Self::Elem) -> (res: usize)
        ensures
            res == self.deep_view().count(value.deep_view()),
    {
        match self.m.get(&value) {
            Some(v) => v.deep_clone(),
            None => 0,
        }
    }
}

impl<T: ObeysDeepEq + std::hash::Hash + std::cmp::Eq> ExecSpecMultisetEmpty for ExecMultiset<T> {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_empty() -> (res: Self)
        ensures
            res.deep_view() =~= Multiset::empty(),
    {
        ExecMultiset { m: HashMap::new() }
    }
}

impl<
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
> ExecSpecMultisetSingleton for ExecMultiset<T> {
    type Elem = T;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_singleton(v: Self::Elem) -> (res: Self)
        ensures
            res.deep_view() =~= Multiset::singleton(v.deep_view()),
    {
        let mut m = HashMap::new();
        m.insert(v.deep_clone(), 1);
        ExecMultiset { m }
    }
}

impl<'a, T> ExecSpecMultisetAdd<'a, ExecMultiset<T>> for &'a ExecMultiset<T> where
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
 {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_add(self, m2: Self) -> (res: ExecMultiset<T>)
        ensures
            res.deep_view() =~= self.deep_view().add(m2.deep_view()),
    {
        let mut add = self.deep_clone();
        for (k, v) in m2.m.iter() {
            if !add.m.contains_key(k) {
                add.m.insert(k.deep_clone(), v.deep_clone());
            } else {
                let new_count = add.m.get(k).unwrap() + v;
                add.m.insert(k.deep_clone(), new_count);
            }
        }
        add
    }
}

impl<'a, T> ExecSpecMultisetSub<'a, ExecMultiset<T>> for &'a ExecMultiset<T> where
    T: ObeysDeepEq + DeepViewClone + std::hash::Hash + std::cmp::Eq,
 {
    #[verifier::external_body]
    #[inline(always)]
    fn exec_sub(self, m2: Self) -> (res: ExecMultiset<T>)
        ensures
            res.deep_view() =~= self.deep_view().sub(m2.deep_view()),
    {
        let mut sub = HashMap::new();
        for (k, v) in self.m.iter() {
            if m2.m.contains_key(k) {
                let v2 = m2.m.get(k).unwrap();
                if v2 < v {
                    sub.insert(k.deep_clone(), v.deep_clone() - v2);
                }
            } else {
                sub.insert(k.deep_clone(), v.deep_clone());
            }
        }
        ExecMultiset { m: sub }
    }
}

} // verus!
