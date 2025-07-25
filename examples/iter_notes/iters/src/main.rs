use vstd::prelude::*;

fn main() { }

verus! {

// Use a module here, so that we can `broadcast use` in the examples further below.
mod iters {

use vstd::prelude::*;

pub enum Operation {
    Next,
    NextBack,
}

pub trait Iter where Self: Sized {
    type Item;

    // Results of calls to next made so far
    spec fn outputs(&self) -> Seq<Option<Self::Item>>;

    spec fn operations(&self) -> Seq<Operation>;

    spec fn inv(&self) -> bool;

    spec fn reaches(&self, dest: Self) -> bool;

    proof fn reaches_reflexive(&self)
        requires
            self.inv(),
        ensures
            self.reaches(*self);

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self)
        requires
            self.inv(),
            iter1.inv(),
            iter2.inv(),
            self.reaches(iter1),
            iter1.reaches(iter2),
        ensures
            self.reaches(iter2);

    proof fn reaches_monotonic(&self, dest: Self)
        requires
            self.inv(),
            dest.inv(),
            self.reaches(dest),
        ensures
            self.outputs().len() <= dest.outputs().len(),
            self.outputs() == dest.outputs().take(self.outputs().len() as int),
        ;

    fn next(&mut self) -> (r: Option<Self::Item>) where Self: core::marker::Sized
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).reaches(*self),
            self.outputs().len() == old(self).outputs().len() + 1,
            self.operations() == old(self).operations().push(Operation::Next),
            r == self.outputs().last(),
        ;
}

pub trait DoubleEndedIter: Iter {
    spec fn outputs_back(&self) -> Seq<Option<Self::Item>>;

    fn next_back(&mut self) -> Option<Self::Item>
        // TODO
        ;
}

pub trait ExactSizeIter: Iter {
    spec fn spec_len(&self) -> nat;

    fn len(&self) -> usize
        // TODO
        ;
}

pub broadcast proof fn reaches_reflexive<I: Iter>(i: I)
    requires
        i.inv(),
    ensures
        #[trigger] i.reaches(i),
{
    i.reaches_reflexive()
}

pub broadcast proof fn reaches_transitive_after_next_if_requested<I: Iter>(i1: I, i2: I, i3: I)
    requires
        i1.inv(),
        i2.inv(),
        i3.inv(),
        i1.reaches(i2),
        #[trigger] i2.reaches(i3),
    ensures
        #[trigger] i1.reaches(i3),
{
    i1.reaches_transitive(i2, i3);
}

}


mod examples {

use vstd::prelude::*;
use crate::iters::*;
broadcast use {reaches_reflexive, reaches_transitive_after_next_if_requested};

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct MyVec<T>(Vec<T>);

impl<T: Copy> MyVec<T> {
    pub uninterp spec fn spec_len(&self) -> int;
    pub uninterp spec fn spec_index(&self, i: int) -> T;

    #[verifier::external_body]
    fn len(&self) -> (r: usize)
        ensures
            r == self.spec_len(),
    {
        todo!()
    }

    #[verifier::external_body]
    fn index(&self, i: usize) -> (r: T)
        requires
            0 <= i < self.spec_len(),
        ensures
            r == self.spec_index(i as int),
    {
        todo!()
    }

    pub open spec fn view(&self) -> Seq<T> {
        Seq::new(self.spec_len() as nat, |i: int| self.spec_index(i))
    }

    fn iter(&self) -> (r: MyVecIter<T>)
        ensures
            r.inv(),
            r.outputs().len() == 0,
            r.pos_back == self@.len(),
            r.next_back_count@ == 0,
            r.vec == &self,
            r.reaches(r),
    {
        let _ = self.len();
        MyVecIter { vec: &self, pos: 0, pos_back: self.len(), next_count: Ghost(0), next_back_count: Ghost(0) }
    }

    spec fn spec_iter(&self) -> MyVecIter<T> {
        MyVecIter { vec: &self, pos: 0, pos_back: self@.len() as usize, next_count: Ghost(0), next_back_count: Ghost(0) }
    }
}

#[verifier::ext_equal]
pub struct MyVecIter<'a, T> {
    pub vec: &'a MyVec<T>,
    pub pos: usize,
    pub pos_back: usize,
    pub next_count: Ghost<int>,
    pub next_back_count: Ghost<int>,
}

impl<'a, T: Copy> Iter for MyVecIter<'a, T> {
    type Item = T;

    open spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        Seq::new(
            self.next_count@ as nat,
            |i: int| if i < self.pos_back { Some(self.vec@[i]) } else { None },
        )
    }

    open spec fn operations(&self) -> Seq<Operation> {
        Seq::new(self.outputs().len(), |_i: int| Operation::Next)
    }

    open spec fn inv(&self) -> bool {
        &&& 0 <= self.pos <= self.pos_back == self.vec@.len()
        &&& self.pos <= self.next_count@
        &&& {
            ||| self.next_count@ == self.pos && 0 <= self.pos < self.pos_back
            ||| self.next_count@ >= self.pos && self.pos == self.pos_back
        }
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        self.vec == dest.vec && self.next_count@ <= dest.next_count@
    }

    proof fn reaches_reflexive(&self) {
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
    }

    proof fn reaches_monotonic(&self, dest: Self) {
    }

    fn next(&mut self) -> (r: Option<Self::Item>)
        ensures
            self.next_count@ == old(self).next_count@ + 1,
            old(self).pos < self.pos_back ==> r == Some(self.vec@[old(self).pos as int]) && self.pos == old(self).pos + 1,
            old(self).pos >= self.pos_back ==> r.is_none() && self.pos == old(self).pos,
// TODO: these need to go through "reaches", not ensures:
// For example, Skip3 needs to say that it reached from iter0 --> iter3 by taking only next steps, not next_back.
// And then vec needs to use this "only-next" information to talk about pos_back.
// Arguably, this "only-next" information is best expressed via:
//   - len of outputs, outputs_back, operations (directly useful if it's all next or all next_back)
//   - elements of operations (clumsily but generally)
            self.pos_back == old(self).pos_back,
            self.next_back_count@ == old(self).next_back_count@,
    {
        proof {
            self.next_count@ = self.next_count@ + 1;
        }
        if self.pos < self.pos_back {
            let _ = self.vec.len(); // HACK
            let i = self.pos;
            self.pos = i + 1;
            Some(self.vec.index(i))
        } else {
            None
        }
    }
}

pub struct Take3<T> {
    pub inner: T,
    pub count: usize,
    pub ghost_count: Ghost<int>,
    pub start_pos: Ghost<int>,
}

impl<T: Iter> Iter for Take3<T> {
    type Item = T::Item;

    open spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        Seq::new(
            self.ghost_count@ as nat,
            |i: int| if i < 3 { self.inner.outputs()[self.start_pos@ + i] } else { None },
        )
    }

    open spec fn operations(&self) -> Seq<Operation> {
        Seq::new(self.outputs().len(), |_i: int| Operation::Next)
    }

    open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@
        &&& self.inner.outputs().len() == self.start_pos@ + self.count
        &&& {
            ||| self.count < 3 && self.count == self.ghost_count@
            ||| self.count == 3 && self.ghost_count@ >= 3
        }
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        &&& self.inner.reaches(dest.inner)
        &&& self.start_pos == dest.start_pos
        &&& self.ghost_count@ <= dest.ghost_count@
    }

    proof fn reaches_reflexive(&self) {
        self.inner.reaches_reflexive()
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
        self.inner.reaches_transitive(iter1.inner, iter2.inner)
    }

    proof fn reaches_monotonic(&self, dest: Self) {
        self.inner.reaches_monotonic(dest.inner)
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        proof {
            self.reaches_reflexive();
            self.ghost_count@ = self.ghost_count@ + 1;
        }
        if self.count < 3 {
            self.count = self.count + 1;
            self.inner.next()
        } else {
            None
        }
    }
}

pub struct Skip3<T> {
    pub inner: T,
    pub has_started: bool,
    pub start_pos: Ghost<int>,
}

impl<T: Iter> Skip3<T> {
    fn new(iter: T) -> (r: Skip3<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            !r.has_started,
            r.inner == iter,
            r.outputs().len() == 0,
    {
        Skip3 { inner: iter, has_started: false, start_pos: Ghost(iter.outputs().len() as int) }
    }

    spec fn spec_new(iter: T) -> Skip3<T> {
        Skip3 { inner: iter, has_started: false, start_pos: Ghost(iter.outputs().len() as int) }
    }
}

impl<T: Iter> Iter for Skip3<T> {
    type Item = T::Item;

    open spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        if self.has_started {
            self.inner.outputs().skip(3 + self.start_pos@)
        } else {
            Seq::empty()
        }
    }

    open spec fn operations(&self) -> Seq<Operation> {
        Seq::new(self.outputs().len(), |_i: int| Operation::Next)
    }

    open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@
        &&& !self.has_started ==> self.start_pos@ == self.inner.outputs().len()
        &&& self.has_started ==> self.start_pos@ + 3 <= self.inner.outputs().len()
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        self.inner.reaches(dest.inner) && self.start_pos == dest.start_pos
    }

    proof fn reaches_reflexive(&self) {
        self.inner.reaches_reflexive()
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
        self.inner.reaches_transitive(iter1.inner, iter2.inner)
    }

    proof fn reaches_monotonic(&self, dest: Self) {
        self.inner.reaches_monotonic(dest.inner)
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        if !self.has_started {
            let _ = self.inner.next();
            let _ = self.inner.next();
            let _ = self.inner.next();
            self.has_started = true;
        }
        self.inner.next()
    }
}

fn test0(v: &MyVec<u8>)
    requires
        v@.len() == 10,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
        v@[7] == 70,
        v@[8] == 80,
        v@[9] == 90,
{
    let mut iter = v.iter();
    let r = iter.next();
    assert(r == Some(0u8));
}

fn test_loop0(v: &MyVec<u8>) {
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = v.iter();
    let ghost i0 = iter;
    loop
        invariant_except_break
            0 <= iter.outputs().len() <= v@.len(), // should be a for loop auto-invariant
            s =~= v@.take(iter.outputs().len() as int),
        invariant
            i0 == v.spec_iter(), // should be a for loop auto-invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.pos_back == iter.vec@.len(), // should be a for loop auto-invariant
        ensures
            s =~= v@,
        decreases v@.len() - iter.outputs().len(),
    {
        if let Some(r) = iter.next() {
            proof {
                s = s.push(r);
            }
        } else {
            break;
        }
    }
    assert(s == v@);
}

#[verifier::loop_isolation(false)]
fn test_loop0_iso_false(v: &MyVec<u8>) {
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = v.iter();
    let ghost i0 = iter;
    loop
        invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.pos_back == iter.vec@.len(), // should be a for loop auto-invariant
            0 <= iter.outputs().len() <= v@.len(), // should be a for loop auto-invariant
            s =~= v@.take(iter.outputs().len() as int),
        decreases v@.len() - iter.outputs().len(),
    {
        if let Some(r) = iter.next() {
            proof {
                s = s.push(r);
            }
        } else {
            break;
        }
    }
    assert(s == v@);
}

fn test1(v: &MyVec<u8>)
    requires
        v@.len() == 10,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
        v@[7] == 70,
        v@[8] == 80,
        v@[9] == 90,
{
    let mut iter = Skip3::new(Skip3::new(v.iter()));
    let r = iter.next();
    assert(r == Some(60u8));
    let r = iter.next();
    assert(r == Some(70u8));
    let r = iter.next();
    assert(r == Some(80u8));
    let r = iter.next();
    assert(r == Some(90u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test3(v: &MyVec<u8>)
    requires
        v@.len() >= 6,
{
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = Skip3::new(Skip3::new(v.iter()));
    let ghost i0 = iter;
    loop
        invariant_except_break
            0 <= iter.outputs().len() <= v@.len() - 6, // should be a for loop auto-invariant
            s =~= v@.skip(6).take(iter.outputs().len() as int),
        invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.inner.inner.pos_back == iter.inner.inner.vec@.len(), // should be a for loop auto-invariant
            i0 == Skip3::spec_new(Skip3::spec_new(v.spec_iter())), // should be a for loop auto-invariant
        ensures
            s =~= v@.skip(6),
        decreases v@.len() - 6 - iter.outputs().len(),
    {
        if let Some(r) = iter.next() {
            proof {
                s = s.push(r);
            }
        } else {
            break;
        }
    }
    assert(s == v@.skip(6));
}

#[verifier::loop_isolation(false)]
fn test3_iso_false(v: &MyVec<u8>)
    requires
        v@.len() >= 6,
{
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = Skip3::new(Skip3::new(v.iter()));
    let ghost i0 = iter;
    loop
        invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.inner.inner.pos_back == iter.inner.inner.vec@.len(), // should be a for loop auto-invariant
            0 <= iter.outputs().len() <= v@.len() - 6, // should be a for loop auto-invariant
            s =~= v@.skip(6).take(iter.outputs().len() as int),
        decreases v@.len() - 6 - iter.outputs().len(),
    {
        if let Some(r) = iter.next() {
            proof {
                s = s.push(r);
            }
        } else {
            break;
        }
    }
    assert(s == v@.skip(6));
}


} // mod examples

} // verus!
