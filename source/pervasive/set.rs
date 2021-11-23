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

#[verifier(no_verify)]
#[proof]
pub fn set_axioms<A>() {
    ensures([
        forall(|a: A| !set_empty().contains(a)),
        forall(|s: Set<A>, a: A| s.insert(a).contains(a)),
        forall(|s: Set<A>, a1: A, a2: A|
            equal(a1, a2) || s.insert(a1).contains(a2) == s.contains(a2)),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a))),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            s1.intersect(s2).contains(a) == s1.contains(a) && s2.contains(a)),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            s1.difference(s2).contains(a) == s1.contains(a) && !s2.contains(a)),
        forall(|s1: Set<A>, s2: Set<A>|
            set_ext_equal(s1, s2) == equal(s1, s2)),
        set_empty::<A>().cardinality() == 0,
        forall(|s: Set<A>, a: A|
            imply(!s.contains(a), #[trigger] s.insert(a).cardinality() == s.cardinality() + 1)),
    ]);
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
