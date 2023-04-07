#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[cfg(not(vstd_build_todo))]
#[allow(unused_imports)]
use crate::pervasive::seq::*;
#[cfg(vstd_build_todo)]
#[allow(unused_imports)]
use crate::seq::*;
extern crate alloc;
use alloc::vec;
#[allow(unused_imports)]
use crate::pervasive::slice::*;

verus! {

#[verifier(external_body)]
pub struct Vec<#[verifier(strictly_positive)] A> {
    pub vec: vec::Vec<A>,
}

impl<A> Vec<A> {
    pub spec fn view(&self) -> Seq<A>;

    #[verifier(external_body)]
    pub fn new() -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec { vec: vec::Vec::new() }
    }

    /// Constructs a new, empty `Vec<A>` with at least the specified capacity. Equivalent to
    /// [`Self::new`], but useful to improve performance when the size is known in advance.
    #[verifier(external_body)]
    pub fn with_capacity(capacity: usize) -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec { vec: vec::Vec::with_capacity(capacity) }
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given `Vec<A>`.
    /// The collection may reserve more space to speculatively avoid frequent reallocations. After
    /// calling reserve, capacity will be greater than or equal to `self.len() + additional`. Does
    /// nothing if capacity is already sufficient.
    #[verifier(external_body)]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.vec.reserve(additional);
    }

    pub fn empty() -> (v: Self)
        ensures
            v@ == Seq::<A>::empty(),
    {
        Vec::new()
    }

    #[verifier(external_body)]
    pub fn push(&mut self, value: A)
        ensures
            self@ == old(self)@.push(value),
    {
        self.vec.push(value);
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (value: A)
        requires
            old(self).len() > 0,
        ensures
            value == old(self)[old(self).len() - 1],
            self@ == old(self)@.subrange(0, old(self).len() - 1),
    {
        unsafe {
            self.vec.pop().unwrap_unchecked()  // Safe to unwrap given the precondition above
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_index(self, i: int) -> A {
        self@[i]
    }

    #[verifier(external_body)]
    #[verifier(autoview)]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.len(),
        ensures
            *r == self[i as int],
    {
        &self.vec[i]
    }

    #[verifier(external_body)]
    pub fn set(&mut self, i: usize, a: A)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, a),
    {
        self.vec[i] = a;
    }

    #[verifier(external_body)]
    pub fn swap(&mut self, i: usize, a: &mut A)
        requires
            i < old(self).len(),
        ensures
            self@ == old(self)@.update(i as int, *old(a)),
            *a == old(self)@.index(i as int)
    {
        core::mem::swap(&mut self.vec[i], a);
    }

    #[verifier(external_body)]
    pub fn insert(&mut self, i: usize, a: A)
        requires
            i <= old(self).len(),
        ensures
            self@ == old(self)@.insert(i as int, a),
    {
        self.vec.insert(i, a);
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, i: usize) -> (r: A)
        requires
            i < old(self).len(),
        ensures
            r == old(self)[i as int],
            self@ == old(self)@.remove(i as int),
    {
        self.vec.remove(i)
    }

    pub spec fn spec_len(&self) -> usize;

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.len(),
    {
        self.vec.len()
    }

    #[verifier(external_body)]
    pub fn as_slice(&self) -> (slice: &[A])
        ensures slice@ == self@
    {
        self.vec.as_slice()
    }

    #[verifier(external_body)]
    pub fn clear(&mut self)
        ensures self.view() == Seq::<A>::empty(),
    {
        self.vec.clear();
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_spec_len<A>(v: Vec<A>)
    ensures
        #[trigger] v.spec_len() == v.view().len(),
{
}

} // verus!
