extern crate builtin;
use builtin::*;

#[verifier(no_verify)]
pub struct Vec<A> {
    pub vec: std::vec::Vec<A>,
}

#[verifier(external)]
fn get_external<A>(v: &Vec<A>, i: usize) -> &A {
    &v.vec[i]
}

#[verifier(external)]
fn set_external<A>(mut v1: Vec<A>, i: usize, a: A) -> Vec<A> {
    v1.vec[i] = a;
    v1
}

/* TODO
#[verifier(external)]
fn length_external<A>(v: &Vec<A>) -> usize {
    v.vec.len()
}
*/

#[verifier(no_verify)]
#[spec]
pub fn len<A>(v: &Vec<A>) -> nat {
    len(v) // TODO: use unimplemented!() here
}

#[verifier(no_verify)]
#[spec]
pub fn index<A>(v: &Vec<A>, i: int) -> A {
    index(v, i) // TODO: use unimplemented!() here
}

#[verifier(no_verify)]
pub fn get<A>(v: &Vec<A>, i: usize) -> &A {
    requires((i as nat) < len(v));
    ensures(|r: A| equal(r, index(v, i)));

    get_external(v, i)
}

#[verifier(no_verify)]
pub fn set<A>(v1: Vec<A>, i: usize, a: A) -> Vec<A> {
    requires((i as nat) < len(&v1));
    ensures(|v2: Vec<A>| [
        len(&v2) == len(&v1),
        equal(a, index(&v2, i)),
        forall(|j: int| imply(0 <= j && j < len(&v1) && j != i, equal(index(&v1, j), index(&v2, j)))),
    ]);

    set_external(v1, i, a)
}
