#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// Axioms for a _finite_ Multiset datatype.
/// Although we represent it as a map from elements to natural numbers,
/// that map must have finite support (i.e., finite number of elements that map to
/// a nonzero value).
///
/// As such, we could in principle implement the Multiset via an inductive datatype
/// and so we can mark its type argument as strictly_positive.

#[verifier(external_body)]
pub struct Multiset<#[verifier(strictly_positive)] V> {
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

    // TODO(tjhance) flesh out remaining proof-mode functions

    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn proof_remove(#[proof] &mut self, #[spec] v: V) -> V {
        requires(old(self).count(v) >= 1);
        ensures(|out_v: V|
            equal(out_v, v) && equal(*self, old(self).remove(v))
        );

        unimplemented!();
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
