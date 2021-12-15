#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

#[verifier(no_verify)]
pub struct Vec<A> {
    pub vec: std::vec::Vec<A>,
}

// TODO(andrea) move into impl once associated functions supported
#[verifier(external)]
fn set_external<A>(mut v: Vec<A>, i: usize, a: A) -> Vec<A> {
    v.vec[i] = a;
    v
}

impl<A> Vec<A> {
    #[verifier(external)]
    fn get_external(&self, i: usize) -> &A {
        &self.vec[i]
    }

    #[verifier(external)]
    fn length_external(&self) -> usize {
        self.vec.len()
    }

    #[verifier(no_verify)]
    #[verifier(pub_abstract)]
    #[spec]
    pub fn view(&self) -> Seq<A> {
        arbitrary()
    }

    // TODO: make this inline
    #[spec]
    pub fn idx(&self, i: int) -> A {
        self.view().index(i)
    }

    #[verifier(no_verify)]
    pub fn get(&self, i: usize) -> &A {
        requires(i < self.view().len());
        ensures(|r: A| equal(r, self.idx(i)));

        self.get_external(i)
    }

    #[verifier(no_verify)]
    pub fn set(self, i: usize, a: A) -> Vec<A> {
        requires(i < self.view().len());
        ensures(|v2: Vec<A>| [
            v2.view().len() == self.view().len(),
            equal(a, v2.idx(i)),
            forall(|j: int| 0 <= j && j < self.view().len() && j != i >>= equal(self.idx(j), v2.idx(j))),
        ]);
        // TODO (once idx is inline): ensures(|v2: Vec<A>| equal(v2.view(), self.view().update(i, a)));

        set_external(self, i, a)
    }

    #[verifier(no_verify)]
    pub fn len(&self) -> usize {
        ensures(|l: usize| l == self.view().len());

        self.length_external()
    }
}
