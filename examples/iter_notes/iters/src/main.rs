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
            self.outputs().is_prefix_of(dest.outputs()),
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

    // TODO: Some form of obeys_spec relating to the fact that next and next_back
    //       are not supposed to pass each other?  
    // Rust docs (https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html) 
    // are ambiguous here.
    fn next_back(&mut self) -> (r: Option<Self::Item>)
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).reaches(*self),
            self.outputs().len() == old(self).outputs().len() + 1,
            self.operations() == old(self).operations().push(Operation::NextBack),
            r == self.outputs().last(),
        ;

    // TODO: Also provides advance_back_by (nightly), nth_back, try_rfold, rfold, rfind
}

pub trait ExactSizeIter: Iter {
    spec fn spec_len(&self) -> nat;

    // TODO: Some form of obeys_spec relating this to operations?  
    // Rust docs (https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html) 
    // are ambiguous here.
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
use vstd::calc;
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


#[verifier::ext_equal]
pub struct MyVecFancyIter<'a, T> {
    pub vec: &'a MyVec<T>,
    pub pos: usize,
    pub pos_back: usize,
    pub next_count: Ghost<int>,
    pub next_back_count: Ghost<int>,
    pub ops: Ghost<Seq<Operation>>,
}

// Sequentially applies each operation to the start/end points, 
// generating a series of elements from contents (or None if start/end meet or exceed contents' bounds).
// Next operations read from `start`; NextBack operations read from `end - 1`
pub open spec fn apply_ops<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int) -> (Seq<Option<T>>, int, int)
    decreases ops.len(),
{
    if ops.len() == 0 {
        (Seq::empty(), start, end)
    } else {
        if 0 <= start < end <= contents.len() {
            match ops.first() {
                Operation::Next => {
                    let (rest, final_start, final_end) = apply_ops(ops.drop_first(), contents, start + 1, end);
                    (seq![Some(contents[start])] + rest, final_start, final_end)
                }
                Operation::NextBack => {
                    let (rest, final_start, final_end) = apply_ops(ops.drop_first(), contents, start, end - 1);
                    (seq![Some(contents[end - 1])] + rest, final_start, final_end)
                }
            }
        } else {
            (Seq::new(ops.len(), |_i| None), start, end)
        }
    }
}

proof fn apply_ops_len<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int)
    ensures 
        apply_ops(ops, contents, start, end).0.len() == ops.len(),
    decreases ops.len(),
{
    if ops.len() == 0 {
    } else {
        apply_ops_len(ops.drop_first(), contents, start + 1, end);
        apply_ops_len(ops.drop_first(), contents, start, end - 1);
    }
}

proof fn apply_ops_extend<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int)
    ensures
        ({
            let (outputs, penultimate_start, penultimate_end) = apply_ops(ops, contents, start, end);
            let (extended, final_start, final_end) = apply_ops(ops.push(Operation::Next), contents, start, end);
            if 0 <= penultimate_start < penultimate_end <= contents.len() {
                &&& extended.last() == Some(contents[penultimate_start])
                &&& final_start == penultimate_start + 1
                &&& final_end == penultimate_end
            } else {
                &&& extended.last() == None::<T>
                &&& final_start == penultimate_start
                &&& final_end == penultimate_end
            }
        }),
{
assume(false);
}


proof fn apply_ops_last<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int)
    requires
        ops.len() > 0,
    ensures
        ({
            let (outputs, final_start, final_end) = apply_ops(ops, contents, start, end);
            outputs.last() == 
                match ops.last() {
                    Operation::Next => 
                        if 0 <= final_start - 1 < final_end <= contents.len() {
                            Some(contents[final_start - 1])
                        } else {
                            None
                        },
                    Operation::NextBack => 
                        if 0 <= final_start < final_end + 1 <= contents.len() {
                            Some(contents[final_end])
                        } else {
                            None
                        }
                    }
        }),
{
assume(false);
}

proof fn apply_ops_monotonic<T>(ops1: Seq<Operation>, ops2: Seq<Operation>, contents: Seq<T>, start:int, end: int)
    requires
        ops1.is_prefix_of(ops2),
    ensures 
        apply_ops(ops1, contents, start, end).0.is_prefix_of(apply_ops(ops2, contents, start, end).0)
    decreases ops1.len(),
{
    if ops1.len() == 0 {
    } else {
        apply_ops_monotonic(ops1.drop_first(), ops2.drop_first(), contents, start + 1, end);
        apply_ops_monotonic(ops1.drop_first(), ops2.drop_first(), contents, start, end - 1);
    }
}

proof fn apply_ops_uniform<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int, cutoff: int)
    requires
        0 <= cutoff <= ops.len(),
        end == contents.len(),
        0 <= start,
        forall |i| 0 <= i < cutoff ==> ops[i] is Next,
    ensures 
        apply_ops(ops.take(cutoff), contents, start, end).0 == 
        Seq::new(
                cutoff as nat,
                |i: int| if start + i < contents.len() { Some(contents[start + i]) } else { None },
            )
    decreases cutoff
{
    if cutoff == 0 {
    } else {
        apply_ops_len(ops.take(cutoff), contents, start, end);
        apply_ops_uniform(ops.take(cutoff), contents, start + 1, end, cutoff - 1);
        assert(ops.take(cutoff).take(cutoff - 1) == ops.take(cutoff).drop_first()); // OBSERVE
    }
}

proof fn apply_ops_uniform_back<T>(ops: Seq<Operation>, contents: Seq<T>, start:int, end: int, cutoff: int)
    requires
        0 <= cutoff <= ops.len(),
        end <= contents.len(),
        0 == start,
        forall |i| 0 <= i < cutoff ==> ops[i] is NextBack,
    ensures 
        apply_ops(ops.take(cutoff), contents, start, end).0 == 
        Seq::new(
                cutoff as nat,
                |i: int| if 0 <= end - i - 1 < contents.len() { Some(contents[end - i - 1]) } else { None },
            )
    decreases cutoff
{
    if cutoff == 0 {
    } else {
        apply_ops_len(ops.take(cutoff), contents, start, end);
        apply_ops_uniform_back(ops.take(cutoff), contents, start, end - 1, cutoff - 1);
        assert(ops.take(cutoff).take(cutoff - 1) == ops.take(cutoff).drop_first()); // OBSERVE
    }
}

impl<'a, T: Copy> Iter for MyVecFancyIter<'a, T> {
    type Item = T;

    open spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        if self.next_back_count == 0 {
            Seq::new(
                self.next_count@ as nat,
                |i: int| if i < self.vec@.len() { Some(self.vec@[i]) } else { None },
            )
        } else if self.next_count == 0 {
            Seq::new(
                self.next_back_count@ as nat,
                |i: int| if i < self.vec@.len() { Some(self.vec@[self.vec@.len() - i - 1]) } else { None },
            )
        } else {
            apply_ops(self.operations(), self.vec@, 0, self.vec@.len() as int).0
        }
    }

    open spec fn operations(&self) -> Seq<Operation> {
        self.ops@
    }

    open spec fn inv(&self) -> bool {
        // The two positions are in bounds and don't pass each other
        &&& 0 <= self.pos <= self.pos_back <= self.vec@.len()
        // pos can't move faster than next_count
        &&& 0 <= self.pos <= self.next_count@
        // pos_back can't move faster than next_back_count
        &&& 0 <= self.next_back_count@ 
        &&& self.next_back_count@ >= self.vec@.len() - self.pos_back
        // All operations have been counted
        &&& self.operations().len() == self.next_count@ + self.next_back_count@
        // In the simple cases, we have a uniform set of operations
        &&& self.next_back_count == 0 <==> (forall |i| 0 <= i < self.operations().len() ==> self.operations()[i] is Next)
        &&& self.next_count == 0 <==> (forall |i| 0 <= i < self.operations().len() ==> self.operations()[i] is NextBack)
        // Possible positions when we've done a modest number of operations and when we've done too many
        &&& {
            ||| self.next_count@ == self.pos && self.pos < self.pos_back
            ||| self.next_count@ >= self.pos && self.pos == self.pos_back
        }
        &&& {
            ||| self.next_back_count@ == self.vec@.len() - self.pos_back && self.pos < self.pos_back
            ||| self.next_back_count@ >= self.vec@.len() - self.pos_back && self.pos == self.pos_back
        }
        &&& {
            let (outputs, start, end) = apply_ops(self.operations(), self.vec@, 0, self.vec@.len() as int);
            outputs == self.outputs() && self.pos == start && self.pos_back == end
        }
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        &&& self.vec == dest.vec 
        &&& self.next_count@ <= dest.next_count@ 
        &&& self.next_back_count@ <= dest.next_back_count@
        &&& self.operations().is_prefix_of(dest.operations())
    }

    proof fn reaches_reflexive(&self) {
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
    }

    proof fn reaches_monotonic(&self, dest: Self) {
        apply_ops_len(self.operations(), self.vec@, 0, self.vec@.len() as int);
        apply_ops_len(dest.operations(), self.vec@, 0, self.vec@.len() as int);
        assert(self.outputs().len() <= dest.outputs().len());
        apply_ops_monotonic(self.operations(), dest.operations(), self.vec@, 0, self.vec@.len() as int);
        if self.next_back_count == 0 {
            if dest.next_back_count == 0 {
            } else if dest.next_count == 0 {
            } else {
                assert forall |i| 0 <= i < self.next_count@ implies dest.operations()[i] is Next by {
                    assert(dest.operations()[i] == self.operations()[i]);   // OBSERVE
                };
                apply_ops_uniform(dest.operations(), self.vec@, 0, self.vec@.len() as int, self.operations().len() as int);
            }
        } else {
            if self.next_count == 0 {
                assert forall |i| 0 <= i < self.next_back_count@ implies dest.operations()[i] is NextBack by {
                    assert(dest.operations()[i] == self.operations()[i]);   // OBSERVE
                };
                apply_ops_uniform_back(dest.operations(), self.vec@, 0, self.vec@.len() as int, self.operations().len() as int);
            } else {
            }
        }
    }

    fn next(&mut self) -> (r: Option<Self::Item>)
    {
        proof {
            apply_ops_len(self.ops@, self.vec@, 0, self.vec@.len() as int);
            self.next_count@ = self.next_count@ + 1;
        }
        self.ops = Ghost(self.ops@.push(Operation::Next));
        proof {
            apply_ops_len(self.ops@, self.vec@, 0, self.vec@.len() as int);
        }
        let r = if self.pos < self.pos_back {
            let _ = self.vec.len(); // HACK
            let i = self.pos;
            self.pos = i + 1;
            Some(self.vec.index(i))
        } else {
            None
        };
        // Prove that `inv` still holds
        assert(!(self.operations().last() is NextBack));    // OBSERVE
        proof {
            if forall |i| 0 <= i < self.operations().len() ==> self.operations()[i] is Next {
                assert forall |i| 0 <= i < old(self).operations().len() implies old(self).operations()[i] is Next by {
                    assert(old(self).operations()[i] == self.operations()[i]);
                }
            }
            apply_ops_extend(old(self).operations(), self.vec@, 0, self.vec@.len() as int);

            let (outputs, start, end) = apply_ops(self.operations(), self.vec@, 0, self.vec@.len() as int);
            assert(self.pos == start && self.pos_back == end);

            if self.next_back_count == 0 {
                apply_ops_uniform(self.operations(), self.vec@, 0, self.vec@.len() as int, self.operations().len() as int);
                assert(self.operations().take(self.operations().len() as int) == self.operations());  // OBSERVE
                assert(outputs == self.outputs());
            } 
        }
        r
    }
}

pub struct Take3<T> {
    pub inner: T,
    pub count: usize,
    pub ghost_count: Ghost<int>,
    pub start_pos: Ghost<int>,
}

impl<T: Iter> Take3<T> {
    fn new(iter: T) -> (r: Take3<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            r.inner == iter,
            r.outputs().len() == 0,
    {
        Take3 { inner: iter, count: 0, ghost_count: Ghost(0), start_pos: Ghost(iter.outputs().len() as int) }
    }

    spec fn spec_new(iter: T) -> Take3<T> {
        Take3 { inner: iter, count: 0, ghost_count: Ghost(0), start_pos: Ghost(iter.outputs().len() as int) }
    }
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

fn test_take3_seq(v: &MyVec<u8>)
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
    let mut iter = Take3::new(v.iter());
    let r = iter.next();
    assert(r == Some(0u8));
    let r = iter.next();
    assert(r == Some(10u8));
    let r = iter.next();
    assert(r == Some(20u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_take3_take3_seq(v: &MyVec<u8>)
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
    let mut iter = Take3::new(Take3::new(v.iter()));
    let r = iter.next();
    assert(r == Some(0u8));
    let r = iter.next();
    assert(r == Some(10u8));
    let r = iter.next();
    assert(r == Some(20u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_skip3_skip3_seq(v: &MyVec<u8>)
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

fn test_skip3_skip3_loop_iso_true(v: &MyVec<u8>)
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
fn test_skip3_skip3_loop_iso_false(v: &MyVec<u8>)
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

fn test_skip3_take3_seq(v: &MyVec<u8>)
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
    let mut iter = Take3::new(Skip3::new(v.iter()));
    let r = iter.next();
    assert(r == Some(30u8));
    let r = iter.next();
    assert(r == Some(40u8));
    let r = iter.next();
    assert(r == Some(50u8));
    let r = iter.next();
    assert(r.is_none());
}

fn test_take3_skip3_seq(v: &MyVec<u8>)
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
    let mut iter = Skip3::new(Take3::new(v.iter()));
    let r = iter.next();
    assert(r.is_none());
}


} // mod examples

} // verus!
