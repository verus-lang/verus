use builtin::*;
use crate::pervasive::*;

/// set type for specifications
#[verifier(no_verify)]
pub struct Set<A> {
    dummy: Vec<A>,
}

//TODO:
//impl<A> Set<A> {
//  ...
//}

#[spec]
#[verifier(pub_abstract)]
pub fn empty<A>() -> Set<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn contains<A>(s: Set<A>, a: A) -> bool {
    arbitrary()
}

#[spec]
pub fn subset_of<A>(s1: Set<A>, s2: Set<A>) -> bool {
    forall(|a: A| imply(contains(s1, a), contains(s2, a)))
}

#[spec]
pub fn ext_equal<A>(s1: Set<A>, s2: Set<A>) -> bool {
    forall(|a: A| contains(s1, a) == contains(s2, a))
}

#[spec]
#[verifier(pub_abstract)]
pub fn insert<A>(s: Set<A>, a: A) -> Set<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn union<A>(s1: Set<A>, s2: Set<A>) -> Set<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn intersect<A>(s1: Set<A>, s2: Set<A>) -> Set<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn difference<A>(s1: Set<A>, s2: Set<A>) -> Set<A> {
    arbitrary()
}

#[spec]
#[verifier(pub_abstract)]
pub fn cardinality<A>(s: Set<A>) -> nat {
    arbitrary()
}

#[verifier(no_verify)]
#[proof]
pub fn set_axioms<A>() {
    ensures([
        forall(|a: A| !contains(empty(), a)),
        forall(|s: Set<A>, a: A| contains(insert(s, a), a)),
        forall(|s: Set<A>, a1: A, a2: A|
            equal(a1, a2) || contains(insert(s, a1), a2) == contains(s, a2)),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            contains(union(s1, s2), a) == (contains(s1, a) || contains(s2, a))),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            contains(intersect(s1, s2), a) == (contains(s1, a) && contains(s2, a))),
        forall(|s1: Set<A>, s2: Set<A>, a: A|
            contains(difference(s1, s2), a) == (contains(s1, a) && !contains(s2, a))),
        forall(|s1: Set<A>, s2: Set<A>|
            ext_equal(s1, s2) == equal(s1, s2)),
        cardinality::<A>(empty()) == 0,
        forall(|s: Set<A>, a: A|
            imply(!contains(s, a),
                //#[trigger]    // TODO(utaal): test framework needs to have #![feature(stmt_expr_attributes)]
                cardinality(insert(s, a)) == cardinality(s) + 1)),
    ]);
}
