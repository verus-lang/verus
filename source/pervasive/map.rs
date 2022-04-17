#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// map type for specifications
#[verifier(external_body)]
pub struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
    dummy: std::marker::PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    fndecl!(pub fn empty() -> Map<K, V>);

    #[spec] #[verifier(publish)]
    pub fn total<F: Fn(K) -> V>(f: F) -> Map<K, V> {
        Set::full().mk_map(f)
    }

    #[spec] #[verifier(publish)]
    pub fn new<FK: Fn(K) -> bool, FV: Fn(K) -> V>(fk: FK, fv: FV) -> Map<K, V> {
        Set::new(fk).mk_map(fv)
    }

    fndecl!(pub fn dom(self) -> Set<K>);

    #[spec] #[verifier(external_body)]
    pub fn index(self, key: K) -> V {
        recommends(self.dom().contains(key));
        unimplemented!()
    }

    fndecl!(pub fn insert(self, key: K, value: V) -> Map<K, V>);

    fndecl!(pub fn remove(self, key: K) -> Map<K, V>);

    #[spec] #[verifier(publish)]
    pub fn ext_equal(self, m2: Map<K, V>) -> bool {
        self.dom().ext_equal(m2.dom()) &&
        forall(|k: K| self.dom().contains(k) >>= equal(self.index(k), m2.index(k)))
    }

    #[spec] #[verifier(publish)]
    pub fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && equal(self.index(k), v)
    }

    #[spec] #[verifier(publish)]
    pub fn le(self, m2: Self) -> bool {
        forall(|k: K| #[trigger] self.dom().contains(k) >>=
            #[trigger] m2.dom().contains(k) && equal(self.index(k), m2.index(k)))
    }

    #[spec] #[verifier(publish)]
    pub fn union_prefer_right(self, m2: Self) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) || m2.dom().contains(k),
            |k: K| if m2.dom().contains(k) { m2.index(k) } else { self.index(k) }
        )
    }

    #[spec] #[verifier(publish)]
    pub fn remove_keys(self, keys: Set<K>) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) && !keys.contains(k),
            |k: K| self.index(k)
        )
    }
}

// Trusted axioms

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_empty<K, V>() {
    ensures(equal(Map::<K, V>::empty().dom(), Set::empty()));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).dom(), m.dom().insert(key)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).index(key), value));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V) {
    requires([
        m.dom().contains(key1),
        !equal(key1, key2),
    ]);
    ensures(equal(m.insert(key2, value).index(key1), m.index(key1)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K) {
    ensures(equal(#[trigger] m.remove(key).dom(), m.dom().remove(key)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K) {
    requires([
        m.dom().contains(key1),
        !equal(key1, key2),
    ]);
    ensures(equal(m.remove(key2).index(key1), m.index(key1)));
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>) {
    ensures(m1.ext_equal(m2) == equal(m1, m2));
}

// Macros

#[macro_export]
macro_rules! map_insert_rec {
    [$val:expr;] => {
        $val
    };
    [$val:expr;$key:expr => $value:expr] => {
        map_insert_rec![$val.insert($key, $value);]
    };
    [$val:expr;$key:expr => $value:expr,$($tail:tt)*] => {
        map_insert_rec![$val.insert($key, $value);$($tail)*]
    }
}

/// Create a map using syntax like `map![key => val, key2 => val, ...]`.

#[macro_export]
macro_rules! map {
    [$($tail:tt)*] => {
        map_insert_rec![$crate::pervasive::map::Map::empty();$($tail)*]
    }
} 
