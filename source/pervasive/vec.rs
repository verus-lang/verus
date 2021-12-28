#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

#[verifier(external_body)]
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
    fn index_external(&self, i: usize) -> &A {
        &self.vec[i]
    }

    #[verifier(external)]
    fn length_external(&self) -> usize {
        self.vec.len()
    }

    #[verifier(external_body)]
    #[verifier(pub_abstract)]
    #[spec]
    pub fn view(&self) -> Seq<A> {
        arbitrary()
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, i: usize) -> &A {
        requires(i < self.view().len());
        ensures(|r: A| equal(r, self.view().index(i)));

        self.index_external(i)
    }

    #[verifier(external_body)]
    pub fn set(self, i: usize, a: A) -> Vec<A> {
        requires(i < self.view().len());
        ensures(|v2: Vec<A>| equal(v2.view(), self.view().update(i, a)));

        set_external(self, i, a)
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn len(&self) -> usize {
        ensures(|l: usize| l == self.view().len());

        self.length_external()
    }
}
