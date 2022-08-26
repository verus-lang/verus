#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;

verus! {

#[verus::verifier(external_body)]
pub struct Vec<#[verus::verifier(strictly_positive)] A> {
    pub vec: std::vec::Vec<A>,
}

impl<A> Vec<A> {
    pub spec fn view(&self) -> Seq<A>;

    #[verus::verifier(external_body)]
    pub fn new() -> (v: Self)
        ensures
            v@ === Seq::empty(),
    {
        Vec { vec: std::vec::Vec::new() }
    }
    
    pub fn empty() -> (v: Self)
        ensures
            v@ === Seq::empty(),
    {
        Vec::new()
    }

    #[verus::verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self@ === old(self)@.push(value),
    {
        self.vec.push(value);
    }

    #[verus::verifier(external_body)]
    pub fn pop(&mut self) -> (value: A)
        requires
            old(self).len() > 0,
        ensures
            value === old(self)[old(self).len() - 1],
            self@ === old(self)@.subrange(0, old(self).len() - 1),
    {
        unsafe {
            self.vec.pop().unwrap_unchecked()  // Safe to unwrap given the precondition above
        }
    }

    #[verus::verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A {
        self@[i]
    }

    #[verus::verifier(external_body)]
    #[verus::verifier(autoview)]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.len(),
        ensures
            *r === self[i as int],
    {
        &self.vec[i]
    }

    #[verus::verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A)
        requires
            i < old(self).len(),
        ensures
            self@ === old(self)@.update(i as int, a),
    {
        self.vec[i] = a;
    }

    pub spec fn spec_len(&self) -> usize;

    #[verus::verifier(external_body)]
    #[verus::verifier(when_used_as_spec(spec_len))]
    #[verus::verifier(autoview)]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.len(),
    {
        self.vec.len()
    }
}

#[verus::verifier(external_body)]
#[verus::verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: Vec<A>)
    ensures
        #[verus::trigger] v.spec_len() == v.view().len(),
{
}

} // verus!
