#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// Axioms for a Multiset datatype. A `Multiset<V>` is effectively a map from elements
/// to natural numbers. A Multiset possibly has an infinite number of elements,
/// though for any element, its number of occurrences will be finite.

#[verifier(external_body)]
pub struct Multiset<#[verifier(maybe_negative)] V> {
    dummy: std::marker::PhantomData<V>,
}

impl<V> Multiset<V> {
    fndecl!(pub fn count(self, value: V) -> nat);

    fndecl!(pub fn empty() -> Self);
    fndecl!(pub fn singleton(v: V) -> Self);
    fndecl!(pub fn add(self, m2: Self) -> Self);
    fndecl!(pub fn sub(self, m2: Self) -> Self);

    #[spec] #[verifier(publish)]
    pub fn insert(self, v: V) -> Self {
        self.add(Self::singleton(v))
    }

    #[spec] #[verifier(publish)]
    pub fn remove(self, v: V) -> Self {
        self.sub(Self::singleton(v))
    }

    #[spec] #[verifier(publish)]
    pub fn le(self, m2: Self) -> bool {
        forall(|v: V| self.count(v) <= m2.count(v))
    }

    #[spec] #[verifier(publish)]
    pub fn ext_equal(self, m2: Self) -> bool {
        forall(|v: V| self.count(v) == m2.count(v))
    }
}

// Specification of `empty`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_empty<V>(v: V) {
    ensures(Multiset::empty().count(v) == 0);
}

// Specification of `singleton`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_singleton<V>(v: V) {
    ensures(Multiset::singleton(v).count(v) == 1);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_singleton_different<V>(v: V, w: V) {
    ensures(!equal(v, w) >>= Multiset::singleton(v).count(w) == 0);
}

// Specification of `add`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_add<V>(m1: Multiset<V>, m2: Multiset<V>, v: V) {
    ensures(m1.add(m2).count(v) == m1.count(v) + m2.count(v));
}

// Specification of `sub`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_sub<V>(m1: Multiset<V>, m2: Multiset<V>, v: V) {
    ensures(m1.sub(m2).count(v) ==
        if m1.count(v) >= m2.count(v) { m1.count(v) - m2.count(v) } else { 0 });
}

// Extensional equality

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_ext_equal<V>(m1: Multiset<V>, m2: Multiset<V>) {
    ensures(m1.ext_equal(m2) == equal(m1, m2));
}
