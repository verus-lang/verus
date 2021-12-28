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

impl<A> Vec<A> {
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

        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(self, i: usize, a: A) -> Vec<A> {
        requires(i < self.view().len());
        ensures(|v2: Vec<A>| equal(v2.view(), self.view().update(i, a)));

        let mut v2 = self;
        v2.vec[i] = a;
        v2
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn len(&self) -> usize {
        ensures(|l: usize| l == self.view().len());

        self.vec.len()
    }
}
