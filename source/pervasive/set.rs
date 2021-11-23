#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;

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
pub fn set_ext_equal<A>(s1: Set<A>, s2: Set<A>) -> bool {
    forall(|a: A| s1.contains(a) == s2.contains(a))
}

impl<A> Set<A> {
    #[spec]
    #[verifier(pub_abstract)]
    pub fn contains(self, a: A) -> bool {
        arbitrary()
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
    pub fn cardinality(self) -> nat {
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
pub fn axiom_set_insert_same<A>(s: Set<A>, a: A) {
    ensures(s.insert(a).contains(a));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A) {
    requires(!equal(a1, a2));
    ensures(s.insert(a1).contains(a2) == s.contains(a2));
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
pub fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>) {
    ensures(set_ext_equal(s1, s2) == equal(s1, s2));
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_empty_cardinality<A>() {
    ensures(set_empty::<A>().cardinality() == 0);
}

#[proof]
#[verifier(no_verify)]
#[verifier(export_as_global_forall)]
pub fn axiom_set_insert_cardinality<A>(s: Set<A>, a: A) {
    requires(!s.contains(a));
    ensures(#[trigger] s.insert(a).cardinality() == s.cardinality() + 1);
}
