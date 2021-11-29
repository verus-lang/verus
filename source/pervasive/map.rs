#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// map type for specifications
#[verifier(no_verify)]
pub struct Map<K, V> {
    dummy: std::marker::PhantomData<(K, V)>,
}

#[spec]
pub fn map_total<K, V, F: Fn(K) -> V>(f: F) -> Map<K, V> {
    set_full().mk_map(f)
}

impl<K, V> Map<K, V> {
    #[spec]
    #[verifier(pub_abstract)]
    pub fn dom(self) -> Set<K> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn index(self, key: K) -> V {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn insert(self, key: K, value: V) -> Map<K, V> {
        arbitrary()
    }

    #[spec]
    pub fn ext_equal(self, m2: Map<K, V>) -> bool {
        self.dom().ext_equal(m2.dom()) &&
        forall(|k: K| imply(self.dom().contains(k), equal(self.index(k), m2.index(k))))
    }
}

// Trusted axioms

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).dom(), m.dom().insert(key)));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V) {
    ensures(equal(#[trigger] m.insert(key, value).index(key), value));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V) {
    requires([
        m.dom().contains(key1),
        !equal(key1, key2),
    ]);
    ensures(equal(m.insert(key2, value).index(key1), m.index(key1)));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>) {
    ensures(m1.ext_equal(m2) == equal(m1, m2));
}
