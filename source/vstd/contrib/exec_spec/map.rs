//! This module contains [`Map`]-specific method implementations.
use crate::contrib::exec_spec::*;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

verus! {

// Note: many of the exec translations are currently unverified, even though the exec functions have specs in vstd.
// This is because HashMap<K, V>::deep_view() is quite hard to work with.
// E.g., the correctness of the translations requires reasoning that K::deep_view() does not create collisions.
broadcast use {
    crate::group_vstd_default,
    crate::std_specs::hash::group_hash_axioms,
    crate::std_specs::hash::lemma_hashmap_deepview_dom
};

/// Impls for shared traits
impl<
    'a,
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
> ToRef<&'a HashMap<K, V>> for &'a HashMap<K, V> {
    #[inline(always)]
    fn get_ref(self) -> &'a HashMap<K, V> {
        &self
    }
}

impl<
    'a,
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
> ToOwned<HashMap<K, V>> for &'a HashMap<K, V> {
    #[verifier::external_body]
    #[inline(always)]
    fn get_owned(self) -> HashMap<K, V> {
        let mut new_map = HashMap::new();
        for (k, v) in self.iter() {
            new_map.insert(k.deep_clone(), v.deep_clone());
        }
        new_map
    }
}

impl<
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
> DeepViewClone for HashMap<K, V> {
    #[verifier::external_body]
    #[inline(always)]
    fn deep_clone(&self) -> Self {
        let mut new_map = HashMap::new();
        for (k, v) in self.iter() {
            new_map.insert(k.deep_clone(), v.deep_clone());
        }
        new_map
    }
}

impl<
    'a,
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
> ExecSpecEq<'a> for &'a HashMap<K, V> where
    &'a K: ExecSpecEq<'a, Other = &'a K>,
    &'a V: ExecSpecEq<'a, Other = &'a V>,
 {
    type Other = &'a HashMap<K, V>;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_eq(this: Self, other: Self::Other) -> bool {
        if this.len() != other.len() {
            return false;
        }
        for (k, v) in this.iter() {
            match other.get(k) {
                Some(ov) => {
                    if !<&'a V>::exec_eq(v, ov) {
                        return false;
                    }
                },
                None => return false,
            }
        }
        true
    }
}

impl<
    'a,
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
> ExecSpecLen for &'a HashMap<K, V> {
    #[inline(always)]
    #[verifier::external_body]
    fn exec_len(self) -> (res: usize)
        ensures
            res == self.deep_view().len(),
    {
        self.len()
    }
}

/// Traits for Map methods
/// Spec for executable version of [`Map::empty`].
pub trait ExecSpecMapEmpty: Sized {
    fn exec_empty() -> Self;
}

// todo: this only works for primtive key types right now
/// Spec for executable version of [`Map`] indexing.
pub trait ExecSpecMapIndex<'a>: Sized + DeepView<
    V = Map<<Self::Key as DeepView>::V, <Self::Value as DeepView>::V>,
> {
    type Key: DeepView;

    type Value: DeepView;

    fn exec_index(self, key: Self::Key) -> Self::Value
        requires
            self.deep_view().dom().contains(key.deep_view()),
    ;
}

/// Spec for executable version of [`Map::insert`].
pub trait ExecSpecMapInsert<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Key: DeepView + DeepViewClone;

    type Value: DeepView + DeepViewClone;

    fn exec_insert(self, key: Self::Key, value: Self::Value) -> Out;
}

/// Spec for executable version of [`Map::remove`].
pub trait ExecSpecMapRemove<'a, Out: Sized + DeepView>: Sized + DeepView + ToOwned<Out> {
    type Key: DeepView + DeepViewClone;

    fn exec_remove(self, key: Self::Key) -> Out;
}

/// Spec for executable version of [`Map::dom`].
pub trait ExecSpecMapDom<'a>: Sized + DeepView {
    type Key: DeepView + DeepViewClone;

    fn exec_dom(self) -> HashSet<Self::Key>;
}

/// Spec for executable version of [`Map::get`].
pub trait ExecSpecMapGet<'a>: Sized + DeepView {
    type Key: DeepView + DeepViewClone;

    type Value: DeepView + DeepViewClone;

    fn exec_get(self, k: Self::Key) -> Option<Self::Value>;
}

/// Impls for executable versions of Map methods
impl<K: DeepView + std::hash::Hash + std::cmp::Eq, V: DeepView> ExecSpecMapEmpty for HashMap<K, V> {
    #[inline(always)]
    fn exec_empty() -> (res: Self)
        ensures
            res.deep_view() =~= Map::empty(),
    {
        HashMap::new()
    }
}

impl<'a, K: DeepView + std::hash::Hash + std::cmp::Eq, V: DeepView> ExecSpecMapIndex<
    'a,
> for &'a HashMap<K, V> {
    type Key = K;

    type Value = &'a V;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_index(self, index: Self::Key) -> (res: Self::Value)
        ensures
            res.deep_view() == self.deep_view()[index.deep_view()],
    {
        self.get(&index).unwrap()
    }
}

impl<'a, K, V> ExecSpecMapInsert<'a, HashMap<K, V>> for &'a HashMap<K, V> where
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
 {
    type Key = K;

    type Value = V;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_insert(self, key: Self::Key, value: Self::Value) -> (res: HashMap<K, V>)
        ensures
            res.deep_view() =~= self.deep_view().insert(key.deep_view(), value.deep_view()),
    {
        let mut m = self.deep_clone();
        let _ = m.insert(key.deep_clone(), value.deep_clone());
        m
    }
}

impl<'a, K, V> ExecSpecMapRemove<'a, HashMap<K, V>> for &'a HashMap<K, V> where
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
 {
    type Key = K;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_remove(self, key: Self::Key) -> (res: HashMap<K, V>)
        ensures
            res.deep_view() =~= self.deep_view().remove(key.deep_view()),
    {
        let mut m = self.deep_clone();
        let _ = m.remove(&key);
        m
    }
}

impl<'a, K, V> ExecSpecMapDom<'a> for &'a HashMap<K, V> where
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
 {
    type Key = K;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_dom(self) -> (res: HashSet<K>)
        ensures
            res.deep_view() =~= self.deep_view().dom(),
    {
        let mut m = HashSet::new();
        for key in self.keys() {
            m.insert(key.deep_clone());
        }
        m
    }
}

impl<'a, K, V> ExecSpecMapGet<'a> for &'a HashMap<K, V> where
    K: DeepView + DeepViewClone + std::hash::Hash + std::cmp::Eq,
    V: DeepView + DeepViewClone,
 {
    type Key = K;

    type Value = V;

    #[verifier::external_body]
    #[inline(always)]
    fn exec_get(self, k: Self::Key) -> (res: Option<Self::Value>)
        ensures
            match (res, self.deep_view().get(k.deep_view())) {
                (Some(v1), Some(v2)) => v1.deep_view() == v2,
                (None, None) => true,
                (_, _) => false,
            },
    {
        self.get(&k).map(|v| v.deep_clone())
    }
}

} // verus!
