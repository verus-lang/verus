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
    pub fn len(&self) -> nat {
        self.view().len()
    }

    // TODO: make this inline
    #[spec]
    pub fn index(&self, i: int) -> A {
        self.view().index(i)
    }

    #[verifier(no_verify)]
    pub fn get(&self, i: usize) -> &A {
        requires(i < self.len());
        ensures(|r: A| equal(r, self.index(i)));

        self.get_external(i)
    }

    #[verifier(no_verify)]
    pub fn set(self, i: usize, a: A) -> Vec<A> {
        requires(i < self.len());
        ensures(|v2: Vec<A>| [
            v2.len() == self.len(),
            equal(a, v2.index(i)),
            forall(|j: int| imply(0 <= j && j < self.len() && j != i, equal(self.index(j), v2.index(j)))),
        ]);
        // TODO (once len and index are inline): ensures(|v2: Vec<A>| equal(v2.view(), self.view().update(i, a)));

        set_external(self, i, a)
    }

    #[verifier(no_verify)]
    pub fn length(&self) -> usize {
        ensures(|l: usize| l == self.len());

        self.length_external()
    }
}
