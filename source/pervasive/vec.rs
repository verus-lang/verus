#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

#[verifier(external_body)]
pub struct Vec<#[verifier(strictly_positive)] A> {
    pub vec: std::vec::Vec<A>,
}

impl<A> Vec<A> {
    fndecl!(pub fn view(&self) -> Seq<A>);

    #[verifier(external_body)]
    pub fn new() -> Self {
        ensures(|v: Self| equal(v.view(), Seq::empty()));

        Vec { vec: std::vec::Vec::new() }
    }
    
    pub fn empty() -> Self {
        ensures(|v: Self| equal(v.view(), Seq::empty()));

        Vec::new()
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A) {
        ensures(equal(self.view(), old(self).view().push(value)));
        self.vec.push(value);
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> A {
        requires(old(self).len() > 0);
        ensures(|value| equal(self.view().push(value), old(self).view()));
        self.vec.pop().unwrap_unchecked()  // Safe to unwrap given the precondition above
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, i: usize) -> &A {
        requires(i < self.view().len());
        ensures(|r: A| equal(r, self.view().index(i)));

        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A) {
        requires(i < old(self).view().len());
        ensures(equal(self.view(), old(self).view().update(i, a)));

        self.vec[i] = a;
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn len(&self) -> usize {
        ensures(|l: usize| l == self.view().len());

        self.vec.len()
    }
}
