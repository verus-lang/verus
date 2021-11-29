#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::map::*;

/// set type for specifications
#[verifier(no_verify)]
pub struct Set<A> {
    dummy: std::marker::PhantomData<A>,
}

// TODO(andrea) move into impl once associated functions supported
#[spec]
#[verifier(pub_abstract)]
pub fn set_empty<A>() -> Set<A> {
    arbitrary()
}

#[spec]
pub fn set_full<A>() -> Set<A> {
    set_empty().complement()
}

#[spec]
#[verifier(pub_abstract)]
pub fn set_new<A, F: Fn(A) -> bool>(f: F) -> Set<A> {
    arbitrary()
}

impl<A> Set<A> {
    #[spec]
    #[verifier(pub_abstract)]
    pub fn contains(self, a: A) -> bool {
        arbitrary()
    }

    #[spec]
    pub fn ext_equal(self, s2: Set<A>) -> bool {
        forall(|a: A| self.contains(a) == s2.contains(a))
    }

    #[spec]
    pub fn subset_of(self, s2: Set<A>) -> bool {
        forall(|a: A| imply(self.contains(a), s2.contains(a)))
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn insert(self, a: A) -> Set<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn union(self, s2: Set<A>) -> Set<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn intersect(self, s2: Set<A>) -> Set<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn difference(self, s2: Set<A>) -> Set<A> {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn complement(self) -> Set<A> {
        arbitrary()
    }

    #[spec]
    pub fn filter<F: Fn(A) -> bool>(self, f: F) -> Set<A> {
        self.intersect(set_new(f))
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn finite(self) -> bool {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn cardinality(self) -> nat {
        arbitrary()
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn mk_map<V, F: Fn(A) -> V>(self, f: F) -> Map<A, V> {
        arbitrary()
    }
}

// Trusted axioms

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_empty<A>(a: A) {
    ensures(!set_empty().contains(a));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_new<A, F: Fn(A) -> bool>(f: F, a: A) {
    ensures(set_new(f).contains(a) == f(a));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_same<A>(s: Set<A>, a: A) {
    ensures(#[trigger] s.insert(a).contains(a));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A) {
    requires(!equal(a1, a2));
    ensures(s.insert(a2).contains(a1) == s.contains(a1));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A) {
    ensures(s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A) {
    ensures(s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A) {
    ensures(s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_complement<A>(s: Set<A>, a: A) {
    ensures(s.complement().contains(a) == !s.contains(a));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>) {
    ensures(s1.ext_equal(s2) == equal(s1, s2));
}

// Note: we could add more axioms about finite and cardinality, but they would be incomplete.
// axiom_set_empty_cardinality, axiom_set_insert_cardinality, and axiom_set_ext_equal are enough
// to build libraries about finite and cardinality.
#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_empty_finite<A>() {
    ensures([
        #[trigger] set_empty::<A>().finite(),
    ]);
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_empty_cardinality<A>() {
    ensures([
        #[trigger] set_empty::<A>().cardinality() == 0,
    ]);
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_finite<A>(s: Set<A>, a: A) {
    requires([
        s.finite(),
    ]);
    ensures([
        #[trigger] s.insert(a).finite(),
    ]);
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_cardinality<A>(s: Set<A>, a: A) {
    requires([
        s.finite(),
        !s.contains(a),
    ]);
    ensures([
        #[trigger] s.insert(a).cardinality() == s.cardinality() + 1
    ]);
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_mk_map_domain<K, V, F: Fn(K) -> V>(s: Set<K>, f: F) {
    ensures(equal(#[trigger] s.mk_map(f).dom(), s));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_mk_map_index<K, V, F: Fn(K) -> V>(s: Set<K>, f: F, key: K) {
    requires(s.contains(key));
    ensures(equal(s.mk_map(f).index(key), f(key)));
}
