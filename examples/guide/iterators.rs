#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::std_specs::iter::{
    DoubleEndedIteratorSpecImpl, ExactSizeIteratorSpecImpl, IteratorSpec, IteratorSpecImpl,
};
use vstd::proph::ProphecyGhost;
use vstd::modes::tracked_swap;

verus! {

// ANCHOR: iter_def
pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
    j: usize,
}

impl <'a, T> VecIterator<'a, T> {
    pub closed spec fn elts(self) -> Seq<T> {
        self.v@
    }

    pub closed spec fn elts_remaining(&self) -> Seq<&'a T>
    {
        self.v@.subrange(self.i as int, self.j as int).as_ref()
    }

    #[verifier::type_invariant]
    pub closed spec fn vec_iterator_type_inv(self) -> bool {
        self.i <= self.j <= self.v.len()
    }
}
// ANCHOR_END: iter_def

impl<'a, T> ExactSizeIteratorSpecImpl for VecIterator<'a, T> {
    open spec fn exact_len(&self) -> usize {
        self.elts_remaining().len() as usize
    }
}

impl<'a, T> ExactSizeIterator for VecIterator<'a, T> {
    fn len(&self) -> usize {
        proof { use_type_invariant(self); }
        self.j - self.i
    }
}

impl <'a, T> VecIterator<'a, T> {
    pub open spec fn peek_front(&self, index: int) -> Option<&'a T> {
        if 0 <= index < self.elts_remaining().len() {
            Some(self.elts_remaining()[index])
        } else {
            None
        }
    }

    pub open spec fn peek_back(&self, index: int) -> Option<&'a T> {
        if 0 <= index < self.elts_remaining().len() {
            Some(self.elts_remaining()[self.elts_remaining().len() - index - 1])
        } else {
            None
        }
    }

    // This proof establishes that the prophetic `self.remaining()` is
    // equivalent to the non-prophetic `self.elts_remaining()`.
    proof fn lemma_elts_remaining_matches_remaining(&self)
        ensures
            self.elts_remaining() == IteratorSpec::remaining(self),
    {
    }
}

// ANCHOR: iter_creation
pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures 
        IteratorSpec::remaining(&iter) == v@.as_ref(),
        IteratorSpec::remaining(&iter).unref() == iter.elts(),
        IteratorSpec::decrease(&iter) is Some,
        iter.elts_remaining() == v@.as_ref(),
{
    VecIterator { v: v, i: 0, j: v.len() }
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
        self.v@.subrange(self.i as int, self.j as int).as_ref()
    }

    closed spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some((self.j - self.i) as nat)
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

// ANCHOR: double_iter_next_back
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
// ANCHOR_END: double_iter_next_back


// ANCHOR: double_iter_spec
impl<'a, T> DoubleEndedIteratorSpecImpl for VecIterator<'a, T> {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = self.elts().len();
        if 0 <= index < len {
            Some(&self.elts()[len - index - 1])
        } else {
            None
        }
    }    
}
// ANCHOR_END: double_iter_spec


fn test_basic() {
    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = Vec::new();

    for x in iter: vec_iter(&v)
        invariant
            w.len() == iter.index(),
            forall |i| 0 <= i < w.len() ==> w@[i] == *iter.seq()[i],
    {
        w.push(*x);
    }
    assert(w.len() == v.len());
    assert(w@ == v@);
}

fn test_next() {
    let values = vec![10u64, 20u64, 30u64, 40u64];
    let mut iter = vec_iter(&values);

    let len = iter.len();
    assert(len == 4);
    let next = iter.next();
    assert(next == Some(&10));
    let len = iter.len();
    assert(len == 3);
    let next = iter.next_back();
    assert(next == Some(&40));
    let len = iter.len();
    assert(len == 2);
    let next = iter.next_back();
    assert(next == Some(&30));
    let next = iter.next();
    assert(next == Some(&20));
    let len = iter.len();
    assert(len == 0);
    let next = iter.next();
    assert(next is None);
    let next = iter.next_back();
    assert(next is None);
}

// ANCHOR: usage_example
fn all_positive(v: &Vec<u8>) -> (b: bool)
    ensures
        b <==> (forall|i: int| 0 <= i < v.len() ==> v[i] > 0),
{
    let mut b: bool = true;

    for x in iter: vec_iter(v)
        invariant
            b <==> (forall|i: int| 0 <= i < iter.index() ==> v[i] > 0),
    {
        b = b && *x > 0;
    }
    b
}
// ANCHOR_END: usage_example

// ANCHOR: build_range
fn build_range(n: u32) -> (v: Vec<u32>)
    ensures
        v.len() == n,
        forall|i: int| 0 <= i < n ==> v[i] == i,
{
    let mut v: Vec<u32> = Vec::new();
    for i in r_iter: 0..n
        invariant
            v.len() == r_iter.index(),
            forall|j: int| 0 <= j < v.len() ==> v[j] == r_iter.seq()[j],
    {
        v.push(i);
    }
    v
}
// ANCHOR_END: build_range

// ANCHOR: no_binding
fn sum_multiples_of_3() -> u64 {
    let mut n: u64 = 0;
    for x in 0..10
        invariant n == x * 3,
    {
        n += 3;
    }
    assert(n == 30);
    n
}
// ANCHOR_END: no_binding

// ANCHOR: rev_example
fn test_reversed(v: &Vec<u8>) -> (w: Vec<u8>)
    ensures
        w@ == v@.reverse(),
{
    let mut w: Vec<u8> = Vec::new();
    for x in iter: v.iter().rev()
        invariant
            w.len() == iter.index(),
            forall|i: int| 0 <= i < w.len() ==> w@[i] == *iter.seq()[i],
    {
        w.push(*x);
    }
    w
}
// ANCHOR_END: rev_example


//////////////////////////////////////////////////////////////////////
//
//      Infinite Counter
//
//////////////////////////////////////////////////////////////////////

// ANCHOR: ctr_iter_def
struct IterCtr {
    count: u64,
    len: Tracked<ProphecyGhost<nat>>,
}
// ANCHOR_END: ctr_iter_def

// ANCHOR: ctr_new
impl IterCtr {
    fn new() -> (r: Self)
        ensures
            r.count == 0,
    {
        IterCtr {
            count: 0,
            len: Tracked(ProphecyGhost::new())
        }
    }
}
// ANCHOR_END: ctr_new

// ANCHOR: ctr_normal_iter
impl Iterator for IterCtr {
    type Item = u64;

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        proof {
            let tracked mut new = ProphecyGhost::new();
            tracked_swap(&mut new, &mut self.len);
            new.resolve_dependent(&self.len, |x:nat| (x + 1) as nat);
            // We learn: old(self).len().value() == final(self).len().value() + 1
        }
        let ret = self.count;
        if self.count == u64::MAX {
            self.count = 0;
        } else {
            self.count = self.count + 1;
        }
        Some(ret)
    }
}
// ANCHOR_END: ctr_normal_iter

// ANCHOR: ctr_iter_spec
impl IteratorSpecImpl for IterCtr {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        Seq::new(self.len@.value(), |i:int| ((i + self.count) % (u64::MAX as int + 1)) as u64)
    }

    open spec fn will_return_none(&self) -> bool { false }

    open spec fn decrease(&self) -> Option<nat> { None }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        Some((index % (u64::MAX as int + 1)) as u64)
    }
}
// ANCHOR_END: ctr_iter_spec

// ANCHOR: ctr_usage_example
#[verifier::exec_allows_no_decreases_clause]
fn infinite_ctr() {
    for x in iter: IterCtr::new()
    {
        assert(x == iter.index@ % (u64::MAX as int + 1));
    }
}
// ANCHOR_END: ctr_usage_example


//////////////////////////////////////////////////////////////////////
//
//      Always 42 ... 43
//
//////////////////////////////////////////////////////////////////////

// ANCHOR: inf_dbl_def
struct Iter42_43 {
    // Number of 42s that will (prophetically) still be handed out by `next`
    front: Tracked<ProphecyGhost<nat>>,
    // Number of 43s that will (prophetically) still be handed out by `next_back`
    back: Tracked<ProphecyGhost<nat>>,
}
// ANCHOR_END: inf_dbl_def

/// Popping a 42 off the front is the same as decrementing `front`.
proof fn lemma_seq_42_43_drop_first(front: nat, back: nat)
    ensures
        seq_42_43((front + 1) as nat, back).drop_first() == seq_42_43(front, back),
{
    assert(seq_42_43((front + 1) as nat, back).drop_first() =~= seq_42_43(front, back));
}

/// Popping a 43 off the back is the same as decrementing `back`.
proof fn lemma_seq_42_43_drop_last(front: nat, back: nat)
    ensures
        seq_42_43(front, (back + 1) as nat).drop_last() == seq_42_43(front, back),
{
    assert(seq_42_43(front, (back + 1) as nat).drop_last() =~= seq_42_43(front, back));
}

impl Iter42_43 {
    fn new() -> Self {
        Iter42_43 {
            front: Tracked(ProphecyGhost::new()),
            back: Tracked(ProphecyGhost::new()),
        }
    }
}

impl Iterator for Iter42_43 {
    type Item = u32;

    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            ret == Some(42u32),
    {
        proof {
            let tracked mut new = ProphecyGhost::new();
            tracked_swap(&mut new, &mut self.front);
            new.resolve_dependent(&self.front, |x:nat| (x + 1) as nat);
            // We learn: old(self).front.value() == final(self).front.value() + 1,
            // and self.back is untouched, so the 43-suffix is unchanged.
            // Hence remaining() loses exactly its first element, which is a 42,
            // since old(self).front.value() >= 1.
            lemma_seq_42_43_drop_first(self.front@.value(), self.back@.value());
        }
        Some(42)
    }
}


// ANCHOR: inf_dbl_spec
spec fn seq_42_43(front: nat, back: nat) -> Seq<u32> {
    Seq::new((front + back) as nat, |i: int| if i < front { 42u32 } else { 43u32 })
}

impl IteratorSpecImpl for Iter42_43 {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { true }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        seq_42_43(self.front@.value(), self.back@.value())
    }

    open spec fn will_return_none(&self) -> bool { false }

    open spec fn decrease(&self) -> Option<nat> { None }

    open spec fn peek(&self, index: int) -> Option<Self::Item> { Some(42) }
}
// ANCHOR_END: inf_dbl_spec


impl DoubleEndedIterator for Iter42_43 {
    fn next_back(&mut self) -> (ret: Option<Self::Item>)
        ensures
            ret == Some(43u32),
    {
        proof {
            let tracked mut new = ProphecyGhost::new();
            tracked_swap(&mut new, &mut self.back);
            new.resolve_dependent(&self.back, |x:nat| (x + 1) as nat);
            // We learn: old(self).back.value() == final(self).back.value() + 1,
            // and self.front is untouched, so remaining() loses exactly its last
            // element, which is a 43, since old(self).back.value() >= 1.
            lemma_seq_42_43_drop_last(self.front@.value(), self.back@.value());
        }
        Some(43)
    }
}

impl DoubleEndedIteratorSpecImpl for Iter42_43 {
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> { Some(43) }
}


#[verifier::exec_allows_no_decreases_clause]
fn infinite_42_43s() {
    for x in Iter42_43::new() {
        assert(x == 42);
    }
}



} // verus!

fn main() {}
