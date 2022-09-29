#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::map::*;

use crate::hash::HashEq;

verus! {

#[verifier(external_body)]
pub struct Dict<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
    dict: std::collections::HashMap<K, V>,
}

impl<K: HashEq + Structural + std::cmp::Eq + std::hash::Hash, V> Dict<K, V> {
    pub spec fn view(&self) -> Map<K, V>;

    #[verifier(external_body)]
    pub fn new() -> (d: Self)
        ensures d.view() === Map::empty() {

        Dict { dict: std::collections::HashMap::new() }
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: K, value: V) -> (r: crate::pervasive::option::Option<V>)
        ensures r === if old(self)@.dom().contains(key) {
                crate::pervasive::option::Option::Some(old(self).view().index(key))
            } else {
                crate::pervasive::option::Option::None
            },
            self@ === old(self)@.insert(key, value),
    {
        match self.dict.insert(key, value) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &K) -> (r: crate::pervasive::option::Option<V>)
        ensures
            r === if old(self)@.dom().contains(*key) {
                crate::pervasive::option::Option::Some(old(self)@.index(*key))
            } else {
                crate::pervasive::option::Option::None
            },
            self@ === old(self)@.remove(*key),
    {
        match self.dict.remove(key) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn contains(&self, key: &K) -> (r: bool)
        ensures r === self.view().dom().contains(*key),
    {
        match self.dict.get(key) {
            Some(v) => true,
            None => false,
        }
    }

    #[verifier(external_body)]
    pub fn index(&self, key: &K) -> (r: &V)
        requires self@.dom().contains(*key),
        ensures *r === self@.index(*key),
    {
        match self.dict.get(key) {
            Some(v) => &v,
            None => panic!("Never reach here"),
        }
    }
}

}
