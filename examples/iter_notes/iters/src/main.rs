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

pub struct Event<T> {
    pub op: Operation,
    pub v: Option<T>,
}

impl<T> Event<T> {
    pub open spec fn new(op: Operation, v: Option<T>) -> Self {
        Event {op, v }
    }
}

#[verifier::ext_equal]
pub struct Events<T> {
    pub s: Seq<Event<T>>
}

impl<T> Events<T> {
    // Forwarding useful seq operations
    pub open spec fn empty() -> Self { Events { s: Seq::empty() } }
    pub open spec fn len(self) -> nat { self.s.len() }
    pub open spec fn is_prefix_of(self, other: Self) -> bool { self.s.is_prefix_of(other.s) }
    pub open spec fn push(self, e: Event<T>) -> Self { Events { s: self.s.push(e) } }
    pub open spec fn last(self) -> Event<T> { self.s.last() }
    pub open spec fn skip(self, n: int) -> Self { Events { s: self.s.skip(n) } }
    #[verifier::inline]
    pub open spec fn spec_index(self, i: int) -> Event<T> { self.s[i] }

    // Event-specific functionality    
    pub open spec fn new(s: Seq<Event<T>>) -> Self { Events { s } }

    pub open spec fn all_next(self) -> bool {
        forall |i| 0 <= i < self.s.len() ==> #[trigger] self.s[i].op is Next
    }

    pub open spec fn all_next_back(self) -> bool {
        forall |i| 0 <= i < self.s.len() ==> #[trigger] self.s[i].op is NextBack
    }

    // pub open spec fn outputs(self) -> Seq<Option<T>> {
    //     self.s.map_values(|e: Event<T>| e.v)
    // }

    pub open spec fn next_count(self) -> nat {
        self.s.fold_left(0, |acc: nat, e: Event<T>| if e.op is Next { acc + 1 } else { acc })
    }

    pub open spec fn next_back_count(self) -> nat {
        self.s.fold_left(0, |acc: nat, e: Event<T>| if e.op is NextBack { acc + 1 } else { acc })
    }

    pub proof fn append_next(&self, r: Option<T>) -> (s_new: Self)
        ensures
            s_new.s == self.s.push(Event::new(Operation::Next, r)),
            s_new.all_next() <==> self.all_next(),
            s_new.next_count() == self.next_count() + 1,
            s_new.next_back_count() == self.next_back_count(),
            //s_new.outputs() == self.outputs().push(r),
    {
        let s_new = Events { s: self.s.push(Event::new(Operation::Next, r)) };
        if s_new.all_next() {
            assert forall |i| 0 <= i < self.s.len() implies #[trigger] self.s[i].op is Next by {
                assert(self.s[i] == self.s.push(Event::new(Operation::Next, r))[i]);
            }
        }

        assert(s_new.next_count() == self.next_count() + 1) by {
            assert(s_new.s.drop_last() == self.s);
        }

        assert(s_new.next_back_count() == self.next_back_count()) by {
            assert(s_new.s.drop_last() == self.s);
        }

        s_new
    }
}

pub open spec fn all_next<T>(s: Seq<Event<T>>) -> bool {
    forall |i| 0 <= i < s.len() ==> #[trigger] s[i].op is Next
}

pub open spec fn all_next_back<T>(s: Seq<Event<T>>) -> bool {
    forall |i| 0 <= i < s.len() ==> #[trigger] s[i].op is NextBack
}

pub open spec fn outputs<T>(s: Seq<Event<T>>) -> Seq<Option<T>> {
    s.map_values(|e: Event<T>| e.v)
}


pub proof fn all_next_extend_new<T>(s: Seq<Event<T>>, r: Option<T>)
    requires all_next(s),
    ensures all_next(s.push(Event::new(Operation::Next, r))),
{
}
pub proof fn all_next_extend_old<T>(s: Seq<Event<T>>, r: Option<T>)
    requires all_next(s.push(Event::new(Operation::Next, r))),
    ensures all_next(s),
{
    assert forall |i| 0 <= i < s.len() implies #[trigger] s[i].op is Next by {
        assert(s[i] == s.push(Event::new(Operation::Next, r))[i]);
    }
}

pub proof fn extend_events_next<T>(s: Seq<Event<T>>, r: Option<T>) -> (s_new: Seq<Event<T>>)
    ensures
        s_new == s.push(Event::new(Operation::Next, r)),
        all_next(s) <==> all_next(s_new),

{
    let s_new = s.push(Event::new(Operation::Next, r));
    if all_next(s_new) {
        assert forall |i| 0 <= i < s.len() implies #[trigger] s[i].op is Next by {
            assert(s[i] == s.push(Event::new(Operation::Next, r))[i]);
        }
    }
    s_new
}


pub trait Iter where Self: Sized {
    type Item;

    // History of calls to next/next_back made so far
    spec fn events(&self) -> Events<Self::Item>;

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
            self.events().is_prefix_of(dest.events()),
        ;

    fn next(&mut self) -> (r: Option<Self::Item>) where Self: core::marker::Sized
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).reaches(*self),
            self.events() == old(self).events().push(Event::new(Operation::Next, r)),
            self.events().last().v == r,    // REVIEW: Derivable from prev. line, but helps triggering by introducing spec_index on self.events()
        ;
}

pub trait DoubleEndedIter: Iter {
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
            self.events() == old(self).events().push(Event::new(Operation::NextBack, r)),
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

    fn iter(&self) -> (r: MyVecFancyIter<T>)
        ensures
            r.inv(),
            r == self.spec_iter(),  
    {
        let iter = MyVecFancyIter { vec: &self, pos: 0, pos_back: self.len(), events: Ghost(Events::empty()) };
        iter
    }

    spec fn spec_iter(&self) -> MyVecFancyIter<T> {
        MyVecFancyIter { vec: &self, pos: 0, pos_back: self@.len() as usize, events: Ghost(Events::empty()) }
    }
}


#[verifier::ext_equal]
pub struct MyVecFancyIter<'a, T> {
    pub vec: &'a MyVec<T>,
    pub pos: usize,
    pub pos_back: usize,
    pub events: Ghost<Events<T>>,
}

impl<'a, T: Copy> Iter for MyVecFancyIter<'a, T> {
    type Item = T;

    open spec fn events(&self) -> Events<T> {
        self.events@
    }

    open spec fn inv(&self) -> bool {
        // The two positions are in bounds and don't pass each other
        &&& 0 <= self.pos <= self.pos_back <= self.vec@.len()
        // Nice cases for what the outputs look like
        &&& self.events().all_next() ==> 
            (forall |i| 0 <= i < self.events().len() ==>
                #[trigger] self.events()[i].v == if i < self.vec@.len() { Some(self.vec@[i]) } else { None })
        &&& self.events().all_next_back() ==> 
            (forall |i| 0 <= i < self.events().len() ==>
                #[trigger] self.events()[i].v == if i < self.vec@.len() { Some(self.vec@[self.vec@.len() - i - 1]) } else { None })
        // pos can't move faster than next_count
        &&& 0 <= self.pos <= self.events().next_count()
        // pos_back can't move faster than next_back_count
        &&& 0 <= self.events().next_back_count()
        &&& self.events().next_back_count() >= self.vec@.len() - self.pos_back
        // All operations have been counted
        &&& self.events().len() == self.events().next_count() + self.events().next_back_count()
        // In the simple cases, we have a uniform set of operations
        &&& self.events().next_back_count() == 0 <==> self.events().all_next()
        &&& self.events().next_count() == 0 <==> self.events().all_next_back() 
        // Possible positions when we've done a modest number of operations and when we've done too many
        &&& {
            ||| self.events().next_count() == self.pos && self.pos < self.pos_back
            ||| self.events().next_count() >= self.pos && self.pos == self.pos_back
        }
        &&& {
            ||| self.events().next_back_count() == self.vec@.len() - self.pos_back && self.pos < self.pos_back
            ||| self.events().next_back_count() >= self.vec@.len() - self.pos_back && self.pos == self.pos_back
        }
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        &&& self.vec == dest.vec 
        &&& self.events().is_prefix_of(dest.events())
    }

    proof fn reaches_reflexive(&self) {
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
    }

    proof fn reaches_monotonic(&self, dest: Self) {
    }

    fn next(&mut self) -> (r: Option<Self::Item>)
    {
        let r = if self.pos < self.pos_back {
            let _ = self.vec.len(); // HACK
            let i = self.pos;
            self.pos = i + 1;
            Some(self.vec.index(i))
        } else {
            None
        };

        // Record this event
        self.events = Ghost(self.events@.append_next(r));

        r
    }
}

/*
impl<'a, T: Copy> DoubleEndedIter for MyVecFancyIter<'a, T> {
    open spec fn outputs_back(&self) -> Seq<Option<Self::Item>> {
        self.outputs()
    }

    fn next_back(&mut self) -> (r: Option<Self::Item>)
    {
        proof {
            apply_ops_len(self.ops@, self.vec@, 0, self.vec@.len() as int);
            self.next_back_count@ = self.next_back_count@ + 1;
        }
        self.ops = Ghost(self.ops@.push(Operation::NextBack));
        proof {
            apply_ops_len(self.ops@, self.vec@, 0, self.vec@.len() as int);
        }
        let r = if self.pos < self.pos_back {
            let _ = self.vec.len(); // HACK
            let i = self.pos_back - 1;
            self.pos_back = i;
            Some(self.vec.index(i))
        } else {
            None
        };
        // Prove that `inv` still holds
        assert(!(self.operations().last() is Next));    // OBSERVE
        proof {
            if forall |i| 0 <= i < self.operations().len() ==> self.operations()[i] is NextBack {
                assert forall |i| 0 <= i < old(self).operations().len() implies old(self).operations()[i] is NextBack by {
                    assert(old(self).operations()[i] == self.operations()[i]);
                }
            }
            apply_ops_extend_back(old(self).operations(), self.vec@, 0, self.vec@.len() as int);

            let (outputs, start, end) = apply_ops(self.operations(), self.vec@, 0, self.vec@.len() as int);
            assert(self.pos == start && self.pos_back == end);

            if self.next_count == 0 {
                apply_ops_uniform_back(self.operations(), self.vec@, 0, self.vec@.len() as int, self.operations().len() as int);
                assert(self.operations().take(self.operations().len() as int) == self.operations());  // OBSERVE
                assert(outputs == self.outputs());
            } 
        }
        r
    }
}
*/

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
            // NOTE: TODO: Added this to cope with MyVecFancyIter
            //iter.events().all_next(),
        ensures
            r.inv(),
            r.inner == iter,
            r.events().len() == 0,
    {
        Take3 { inner: iter, count: 0, ghost_count: Ghost(0), start_pos: Ghost(iter.events().len() as int) }
    }

    spec fn spec_new(iter: T) -> Take3<T> {
        Take3 { inner: iter, count: 0, ghost_count: Ghost(0), start_pos: Ghost(iter.events().len() as int) }
    }
}

impl<T: Iter> Iter for Take3<T> {
    type Item = T::Item;

    open spec fn events(&self) -> Events<Self::Item> {
        Events::new(
            Seq::new(
                self.ghost_count@ as nat,
                |i: int| if i < 3 { self.inner.events()[self.start_pos@ + i] } else { Event::new(Operation::Next, None) },
            )
        )
    }

    open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@
        &&& self.inner.events().len() == self.start_pos@ + self.count
        &&& {
            ||| self.count < 3 && self.count == self.ghost_count@
            ||| self.count == 3 && self.ghost_count@ >= 3
        }
        // NOTE: Added this to help with MyVecFancyIter
        //&&& self.inner.events().all_next()
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
            let r = self.inner.next();
            r
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
            r.events().len() == 0,
    {
        Skip3 { inner: iter, has_started: false, start_pos: Ghost(iter.events().len() as int) }
    }

    spec fn spec_new(iter: T) -> Skip3<T> {
        Skip3 { inner: iter, has_started: false, start_pos: Ghost(iter.events().len() as int) }
    }
}

impl<T: Iter> Iter for Skip3<T> {
    type Item = T::Item;

    open spec fn events(&self) -> Events<Self::Item> {
        if self.has_started {
            self.inner.events().skip(3 + self.start_pos@)
        } else {
            Events::empty()
        }
    }

    open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@
        &&& !self.has_started ==> self.start_pos@ == self.inner.events().len()
        &&& self.has_started ==> self.start_pos@ + 3 <= self.inner.events().len()
        // We only perform Next operations
        &&& forall |i| self.start_pos@ <= i < self.inner.events().len() ==> (#[trigger] self.inner.events()[i].op) is Next
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


/*
pub struct Rev<T> {
    pub inner: T,
}

impl<T: DoubleEndedIter> Rev<T> {
    fn new(iter: T) -> (r: Rev<T>)
        requires
            iter.inv(),
            // NOTE: TODO: Added this to cope with MyVecFancyIter
            // all_next(iter.operations()),
        ensures
            r.inv(),
            r.inner == iter,
    {
        Rev { inner: iter }
    }

    spec fn spec_new(iter: T) -> Rev<T> {
        Rev { inner: iter }
    }
}

impl<T: DoubleEndedIter> Iter for Rev<T> {
    type Item = T::Item;

    open spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        self.inner.outputs()
    }

    open spec fn operations(&self) -> Seq<Operation> {
        self.inner.operations().map_values(|op| 
            match op { 
                Operation::Next => Operation:: NextBack,
                Operation::NextBack => Operation::Next,
            })
    }

    open spec fn inv(&self) -> bool {
        &&& self.inner.inv()
    }

    open spec fn reaches(&self, dest: Self) -> bool {
        self.inner.reaches(dest.inner)
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
        self.inner.next_back()
    }
}

impl<T: DoubleEndedIter> DoubleEndedIter for Rev<T> {
    open spec fn outputs_back(&self) -> Seq<Option<Self::Item>> {
        self.outputs()
    }

    fn next_back(&mut self) -> (r: Option<Self::Item>) {
        self.inner.next()
    }

}
*/


fn test0_next(v: &MyVec<u8>)
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
    let r = iter.next();
    assert(r == Some(10u8));
}

/*
fn test0_next_back(v: &MyVec<u8>)
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
    let r = iter.next_back();
    assert(r == Some(90u8));
    let r = iter.next_back();
    assert(r == Some(80u8));
}
*/

fn test_loop0(v: &MyVec<u8>) {
    let ghost mut s: Seq<u8> = Seq::empty();

    let mut iter = v.iter();
    let ghost i0 = iter;
    loop
        invariant_except_break
            0 <= iter.events().len() <= v@.len(), // should be a for loop auto-invariant
            s =~= v@.take(iter.events().len() as int),
        invariant
            // NOTE: Needed to add the following line to help with MyVecFancyIter (for-loop iterator could automatically add it):
            iter.events().all_next(),
            i0 == v.spec_iter(), // should be a for loop auto-invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.pos_back == iter.vec@.len(), // should be a for loop auto-invariant
        ensures
            s =~= v@,
        decreases v@.len() - iter.events().len(),
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
            // NOTE: Added this line to help with MyVecFancyIter (for-loop iterator could automatically add it):
            iter.events().all_next(),
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.pos_back == iter.vec@.len(), // should be a for loop auto-invariant
            0 <= iter.events().len() <= v@.len(), // should be a for loop auto-invariant
            s =~= v@.take(iter.events().len() as int),
        decreases v@.len() - iter.events().len(),
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

fn test_skip3_seq(v: &MyVec<u8>)
    requires
        v@.len() == 7,
        v@[0] == 0,
        v@[1] == 10,
        v@[2] == 20,
        v@[3] == 30,
        v@[4] == 40,
        v@[5] == 50,
        v@[6] == 60,
{
    let mut iter = Skip3::new(v.iter());
    let r = iter.next();
    assert(r == Some(30u8));
    let r = iter.next();
    assert(r == Some(40u8));
    let r = iter.next();
    assert(r == Some(50u8));
    let r = iter.next();
    assert(r == Some(60u8));
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
            0 <= iter.events().len() <= v@.len() - 6, // should be a for loop auto-invariant
            s =~= v@.skip(6).take(iter.events().len() as int),
        invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            iter.inner.inner.pos_back == iter.inner.inner.vec@.len(), // should be a for loop auto-invariant
            i0 == Skip3::spec_new(Skip3::spec_new(v.spec_iter())), // should be a for loop auto-invariant
        ensures
            s =~= v@.skip(6),
        decreases v@.len() - 6 - iter.events().len(),
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
            0 <= iter.events().len() <= v@.len() - 6, // should be a for loop auto-invariant
            s =~= v@.skip(6).take(iter.events().len() as int),
        decreases v@.len() - 6 - iter.events().len(),
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

/*
fn all_true<I: Iter<Item=bool>>(iter: &mut I) -> (r: (Ghost<int>, bool))
    requires
        old(iter).outputs().len() == 0,
    ensures
        ({
            let (count, result) = r;
            &&& count == iter.outputs().len()
            &&& result == forall |i| 0 <= i < iter.outputs().len() ==> (#[trigger]iter.outputs()[i] matches Some(b) && b)
        }),
        all_next(iter.operations()),
{
    // TODO
    assume(false);
    (Ghost(0), true)
}
fn all_true_caller(v: &MyVec<bool>)
    requires
        v@.len() == 10,
{
    let mut iter = v.iter();
    let (Ghost(count), b) = all_true(&mut iter);
    proof {
        if count == 10 && b {
            assert(iter.outputs().len() == 10);
            assert(forall |i| 0 <= i < v@.len() ==> (#[trigger]iter.outputs()[i] matches Some(b) && b));
            assert(forall |i| 0 <= i < v@.len() ==> v@[i]);
        }
    }


}

fn test_rev_seq(v: &MyVec<u8>)
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
    let r = iter.next_back();
    assert(r == Some(90u8));
    let mut iter_r = Rev::new(v.iter());
    let r = iter_r.next();
    assert(r is Some);
    assert(r == Some(90u8));
    // let r = iter_r.next();
    // assert(r == Some(80u8));
}
*/

} // mod examples

} // verus!
