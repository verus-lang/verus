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
    fn new() -> Self {
        ensures(|d: Self| equal(d.view(), Map::empty()));

        Dict { dict: std::collections::HashMap::new() }
    }

    pub fn empty() -> Self {
        ensures(|d: Self| equal(d.view(), Map::empty()));

        Dict::new()
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, key: K, value: V) {
        ensures(equal(self.view(), old(self).view().insert(key, value)));

        self.dict.insert(key, value);
    }

    #[verifier(external_body)]
    #[verifier(autoview)]    
    pub fn contain(&self, key: &K) -> bool {
        ensures(|r: bool|[
            r >>= self.view().dom().contains(key),
            self.view().dom().contains(key) >>= r,
            ]);

        match self.dict.get(key) {
            Some(v) => true,
            None => false,
        }
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, key: K) -> &V {
        requires(self.view().dom().contains(key));
        ensures(|r: V| equal(r, self.view().index(key)));

        match self.dict.get(&key) {
            Some(v) => &v,
            None => panic!("Never reach here"),
        }
    }
}
