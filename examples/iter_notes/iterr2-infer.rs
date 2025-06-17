//extern crate vstd;
//extern crate builtin;
//extern crate builtin_macros;

//#![feature(allocator_api)]

#[allow(unused_imports)]use builtin_macros::*;#[allow(unused_imports)]use builtin::*;
#[allow(unused_imports)]use vstd::prelude::*;

fn main() { }

verus! {

trait Iter where Self: Sized {
    type Item;

    // Results of calls to next made so far
    spec fn outputs(&self) -> Seq<Option<Self::Item>>;

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
            self.outputs() =~= dest.outputs().take(self.outputs().len() as int),
        ;

    // for loop invariant inference:
    spec fn init_matches(&self, init: Self) -> bool {
        true
    }

    fn next(&mut self) -> (r: Option<Self::Item>) where Self: core::marker::Sized
        requires
            old(self).inv(),
        ensures
            self.inv(),
            old(self).reaches(*self),
            self.outputs().len() == old(self).outputs().len() + 1,
            r =~= self.outputs().last(),
        ;
}

#[verifier::broadcast_forall]
proof fn reaches_reflexive<I: Iter>(i: I)
    requires
        i.inv(),
    ensures
        #[trigger] i.reaches(i),
{
    i.reaches_reflexive()
}

#[verifier::broadcast_forall]
proof fn reaches_transitive_after_next_if_requested<I: Iter>(i1: I, i2: I, i3: I)
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

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
struct MyVec<T>(Vec<T>);

impl<T: Copy> MyVec<T> {
    spec fn spec_len(&self) -> int;
    spec fn spec_index(&self, i: int) -> T;

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

    spec fn view(&self) -> Seq<T> {
        Seq::new(self.spec_len() as nat, |i: int| self.spec_index(i))
    }

    fn iter(&self) -> (r: MyVecIter<T>)
        ensures
            r.inv(),
            r.outputs().len() == 0,
            r.vec == &self,
            r.reaches(r),
    {
        let _ = self.len();
        MyVecIter { vec: &self, pos: 0, spec_pos: Ghost(0) }
    }

    spec fn spec_iter(&self) -> MyVecIter<T> {
        MyVecIter { vec: &self, pos: 0, spec_pos: Ghost(0) }
    }
}

#[verifier::ext_equal]
struct MyVecIter<'a, T> {
    vec: &'a MyVec<T>,
    pos: usize,
    spec_pos: Ghost<int>,
}

impl<'a, T: Copy> Iter for MyVecIter<'a, T> {
    type Item = T;

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        Seq::new(
            self.spec_pos@ as nat,
            |i: int| if i < self.vec@.len() { Some(self.vec@[i]) } else { None },
        )
    }

    spec fn inv(&self) -> bool {
        &&& {
            ||| self.spec_pos@ == self.pos && 0 <= self.pos < self.vec@.len()
            ||| self.spec_pos@ >= self.pos && self.pos == self.vec@.len()
        }
    }

    spec fn reaches(&self, dest: Self) -> bool {
        self.vec == dest.vec && self.spec_pos@ <= dest.spec_pos@
    }

    proof fn reaches_reflexive(&self) {
    }

    proof fn reaches_transitive(&self, iter1: Self, iter2: Self) {
    }

    proof fn reaches_monotonic(&self, dest: Self) {
    }

    spec fn init_matches(&self, init: Self) -> bool {
        self.vec == init.vec
    }

    fn next(&mut self) -> (r: Option<Self::Item>)
        ensures
            self.spec_pos@ == old(self).spec_pos@ + 1,
            self.spec_pos@ <= self.vec@.len() ==> r == Some(self.vec@[old(self).spec_pos@]),
            self.spec_pos@ > self.vec@.len() ==> r.is_none(),
    {
        proof {
            self.spec_pos@ = self.spec_pos@ + 1;
        }
        if self.pos < self.vec.len() {
            let i = self.pos;
            self.pos = i + 1;
            Some(self.vec.index(i))
        } else {
            None
        }
    }
}

struct Take3<T> {
    inner: T,
    count: usize,
    start_pos: Ghost<int>,
}

impl<T: Iter> Iter for Take3<T> {
    type Item = T::Item;

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        self.inner.outputs().skip(self.start_pos@).map(|i: int, o| if i < 3 { o } else { None })
    }

    spec fn inv(&self) -> bool {
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@ <= self.inner.outputs().len()
        &&& {
            ||| self.count < 3 && self.count == self.outputs().len()
            ||| self.count == 3 && self.outputs().len() >= 3
        }
    }

    spec fn reaches(&self, dest: Self) -> bool {
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

    spec fn init_matches(&self, init: Self) -> bool {
        self.inner.init_matches(init.inner) && self.start_pos == init.start_pos
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        if self.count < 3 {
            self.count = self.count + 1;
            self.inner.next()
        } else {
            // TODO: the real Rust Take iterator doesn't call next here
            let _ = self.inner.next();
            None
        }
    }
}

struct Skip3<T> {
    inner: T,
    start_pos: Ghost<int>,
    has_started: Ghost<bool>, // for loop invariant inference (TODO: get rid of this; lazy iterators don't need it)
}

impl<T: Iter> Skip3<T> {
    fn new(iter: T) -> (r: Skip3<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            r.has_started@,
            r.inner.outputs().len() == iter.outputs().len() + 3,
            r.outputs().len() == 0,
            r.outputs() == r.inner.outputs().skip(3 + r.start_pos@),
            iter.reaches(r.inner),
    {
        reveal(reaches_transitive_after_next_if_requested);
        let mut iter = iter;
        let ghost start_pos = iter.outputs().len();
        // TODO: the real Rust Skip iterator doesn't call next here (it has lazy semantics)
        let _ = iter.next();
        let _ = iter.next();
        let _ = iter.next();
        Skip3 { inner: iter, start_pos: Ghost(start_pos as int), has_started: Ghost(true) }
    }

    spec fn spec_new(iter: T) -> Skip3<T> {
        Skip3 { inner: iter, start_pos: Ghost(iter.outputs().len() as int), has_started: Ghost(false) }
    }
}

impl<T: Iter> Iter for Skip3<T> {
    type Item = T::Item;

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        if self.has_started@ {
            self.inner.outputs().skip(3 + self.start_pos@)
        } else {
            Seq::empty()
        }
    }

    spec fn inv(&self) -> bool {
        &&& self.has_started@
        &&& self.inner.inv()
        &&& 0 <= self.start_pos@
        &&& self.start_pos@ + 3 <= self.inner.outputs().len()
    }

    spec fn reaches(&self, dest: Self) -> bool {
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

    spec fn init_matches(&self, init: Self) -> bool {
        self.inner.init_matches(init.inner) && self.start_pos == init.start_pos
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        self.inner.next()
    }
}

fn test0(v: &MyVec<u8>)
    requires
        v.spec_len() == 10,
        v.spec_index(0) == 0,
        v.spec_index(1) == 10,
        v.spec_index(2) == 20,
        v.spec_index(3) == 30,
        v.spec_index(4) == 40,
        v.spec_index(5) == 50,
        v.spec_index(6) == 60,
        v.spec_index(7) == 70,
        v.spec_index(8) == 80,
        v.spec_index(9) == 90,
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
            i0.init_matches(v.spec_iter()), // should be a for loop auto-invariant
            i0.reaches(iter), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
        ensures
            s =~= v@,
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
            0 <= iter.outputs().len() <= v@.len(), // should be a for loop auto-invariant
            s =~= v@.take(iter.outputs().len() as int),
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
        v.spec_len() == 10,
        v.spec_index(0) == 0,
        v.spec_index(1) == 10,
        v.spec_index(2) == 20,
        v.spec_index(3) == 30,
        v.spec_index(4) == 40,
        v.spec_index(5) == 50,
        v.spec_index(6) == 60,
        v.spec_index(7) == 70,
        v.spec_index(8) == 80,
        v.spec_index(9) == 90,
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
            i0.init_matches(Skip3::spec_new(Skip3::spec_new(v.spec_iter()))), // should be a for loop auto-invariant
        ensures
            s =~= v@.skip(6),
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
            0 <= iter.outputs().len() <= v@.len() - 6, // should be a for loop auto-invariant
            s =~= v@.skip(6).take(iter.outputs().len() as int),
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

} // verus!
