#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::iter::{IteratorSpec,IteratorSpecImpl};

verus! {

// ANCHOR: iter_def
pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
    j: usize,
}

impl <'a, T> VecIterator<'a, T> {
    pub closed spec fn new(v: &'a Vec<T>) -> Self {
        VecIterator { v, i: 0, j: v.len() }
    }

    pub closed spec fn elts(self) -> Seq<T> {
        self.v@
    }

    #[verifier::type_invariant]
    pub closed spec fn vec_iterator_type_inv(self) -> bool {
        &&& self.i <= self.j <= self.v.len()
        &&& self.i <= self.j <= self.v@.len()
    }
}
// ANCHOR_END: iter_def

// ANCHOR: iter_creation
pub open spec fn vec_iter_spec<'a, T>(v: &'a Vec<T>) -> VecIterator<'a, T> {
    VecIterator::new(v)
}

pub broadcast proof fn vec_iter_spec_properties<'a, T>(v: &'a Vec<T>)
    ensures
        #[trigger] vec_iter_spec(v).elts() == v@,
{
}

#[verifier::when_used_as_spec(vec_iter_spec)]
pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures 
        iter == vec_iter_spec(v),
        IteratorSpec::decrease(&iter) is Some,
        IteratorSpec::initial_value_inv(&iter, &vec_iter_spec(v)),
{
    let i = VecIterator { v: v, i: 0, j: v.len() };
    assert(i.elts() == IteratorSpec::remaining(&i).map_values(|v: &T| *v));     // OBSERVE
    i
}
// ANCHOR_END: iter_creation

// ANCHOR: normal_iter
impl<'a, T> Iterator for VecIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> (ret: Option<Self::Item>) 
    {
        proof { use_type_invariant(&*self); }
        if self.i < self.j {
            let i = self.i;
            self.i = self.i + 1;
            return Some(&self.v[i]);
        } else {
            return None;
        }
    }
}
// ANCHOR_END: normal_iter

// ANCHOR: iter_spec
impl<'a, T> IteratorSpecImpl for VecIterator<'a, T> {

    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    closed spec fn remaining(&self) -> Seq<Self::Item> {
        self.v@.subrange(self.i as int, self.j as int).map(|i, v| &v)
    }

    closed spec fn completes(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some((self.j - self.i) as nat)
    }
    
    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& self.elts() == IteratorSpec::remaining(self).map_values(|v: &T| *v)
        &&& init.elts() == self.elts()
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < self.elts().len() {
            Some(&self.elts()[index])
        } else {
            None
        }
    }
}
// ANCHOR_END: iter_spec

// ANCHOR: double_iter_spec
impl<'a, T> DoubleEndedIterator for VecIterator<'a, T> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        proof { use_type_invariant(&*self); }
        if self.i < self.j {
            self.j = self.j - 1;
            return Some(&self.v[self.j]);
        } else {
            return None;
        }
    }
}
// ANCHOR_END: double_iter_spec

fn test_basic() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    for x in iter: vec_iter(&v)
        invariant
            w@ == iter.seq().take(iter.index@).map_values(|v: &u8| *v),
    {
        w.push(*x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);
}

// ANCHOR: usage_example
fn all_positive(v: &Vec<u8>) -> (b: bool)
    ensures
        b <==> (forall|i: int| 0 <= i < v.len() ==> v[i] > 0),
{
    let mut b: bool = true;

    for x in iter: vec_iter(v)
        invariant
            b <==> (forall|i: int| 0 <= i < iter.index@ ==> v[i] > 0),
    {
        b = b && *x > 0;
    }
    b
}
// ANCHOR_END: usage_example

} // verus!

fn main() {}
