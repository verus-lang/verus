#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::map::*;

#[verifier(external_body)]
pub struct Dict<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
    pub dict: std::collections::HashMap<K, V>,
}

impl<K: std::cmp::Eq + std::hash::Hash, V> Dict<K, V> {
    fndecl!(pub fn view(&self) -> Map<K, V>);

    #[verifier(external_body)]
    pub fn new() -> Self {
        ensures(|d: Self| equal(d.view(), Map::empty()));

        Dict { dict: std::collections::HashMap::new() }
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: K, value: V) -> crate::pervasive::option::Option<V> {
        ensures(|r: crate::pervasive::option::Option<V>| [
            equal(r, if old(self).view().dom().contains(key) {
                crate::pervasive::option::Option::Some(old(self).view().index(key))
            } else {
                crate::pervasive::option::Option::None
            }),
            equal(self.view(), old(self).view().insert(key, value)),
        ]);

        match self.dict.insert(key, value) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, key: &K) -> crate::pervasive::option::Option<V> {
        ensures(|r: crate::pervasive::option::Option<V>| [
            equal(r, if old(self).view().dom().contains(*key) {
                crate::pervasive::option::Option::Some(old(self).view().index(*key))
            } else {
                crate::pervasive::option::Option::None
            }),
            equal(self.view(), old(self).view().remove(*key)),
        ]);

        match self.dict.remove(key) {
            Some(v) => crate::pervasive::option::Option::Some(v),
            None => crate::pervasive::option::Option::None,
        }
    }

    #[verifier(external_body)]
    #[verifier(autoview)]    
    pub fn contains(&self, key: &K) -> bool {
        ensures(|r: bool| r == self.view().dom().contains(*key));

        match self.dict.get(key) {
            Some(v) => true,
            None => false,
        }
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, key: &K) -> &V {
        requires(self.view().dom().contains(*key));
        ensures(|r: V| equal(r, self.view().index(*key)));

        match self.dict.get(key) {
            Some(v) => &v,
            None => panic!("Never reach here"),
        }
    }
}
