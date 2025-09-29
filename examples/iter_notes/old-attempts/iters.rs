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
    type State;

    // Results of calls to next made so far
    spec fn outputs(&self) -> Seq<Option<Self::Item>>;

    spec fn states(&self) -> Seq<Self::State>;

    spec fn inv(&self) -> bool {
        self.states().len() == self.outputs().len() + 1
    }

    proof fn inv_well_formed(&self)
        ensures
            self.inv() ==> self.states().len() == self.outputs().len() + 1;

    fn next(&mut self) -> (r: Option<Self::Item>) where Self: core::marker::Sized
        requires
            old(self).inv(),
        ensures
            self.inv(),
            self.states().len() == self.outputs().len() + 1,
            self.outputs().len() == old(self).outputs().len() + 1,
            self.states().len() == old(self).states().len() + 1,
            forall|i: int|
                #![trigger self.outputs()[i]]
                #![trigger self.states()[i]]
                {
                    &&& 0 <= i < old(self).outputs().len() ==> self.states()[i] =~= old(self).states()[i]
                    &&& 0 <= i < self.outputs().len() ==> self.states()[i] =~= old(self).states()[i]
                },
            r =~= self.outputs().last(),
        ;
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
            r.states()[0] == self@,
    {
        let _ = self.len();
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
    type State = Seq<T>;

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        Seq::new(
            self.spec_pos@ as nat,
            |i: int| if i < self.vec@.len() { Some(self.vec@[i]) } else { None },
        )
    }

    spec fn states(&self) -> Seq<Self::State> {
        Seq::new(
            self.spec_pos@ as nat + 1,
            |i: int| self.vec@,
        )
    }

    spec fn inv(&self) -> bool {
        &&& {
            ||| self.spec_pos@ == self.pos && 0 <= self.pos < self.vec@.len()
            ||| self.spec_pos@ >= self.pos && self.pos == self.vec@.len()
        }
    }

    proof fn inv_well_formed(&self) {
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
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

#[verifier::external_body]
fn random_byte() -> u8 {
    todo!()
}

struct RandomByteIter {
    outputs: Ghost<Seq<Option<u8>>>,
}

impl RandomByteIter {
    fn new() -> (r: RandomByteIter)
        ensures
            r.inv(),
            r.outputs().len() == 0,
    {
        RandomByteIter { outputs: Ghost(Seq::empty()) }
    }
}

impl Iter for RandomByteIter {
    type Item = u8;
    type State = ();

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        self.outputs@
    }

    spec fn states(&self) -> Seq<Self::State> {
        Seq::new(self.outputs@.len() + 1, |i: int| ())
    }

    spec fn inv(&self) -> bool {
        self.states().len() == self.outputs().len() + 1
    }

    proof fn inv_well_formed(&self) {
    }

    fn next(&mut self) -> (r: Option<Self::Item>)
        ensures
            r.is_some(),
    {
        let x = random_byte();
        proof {
            self.outputs@ = self.outputs@.push(Some(x));
        }
        Some(x)
    }
}

struct Skip3<T>(T);

impl<T: Iter> Skip3<T> {
    fn new(iter: T) -> (r: Skip3<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            r.states().len() == r.outputs().len() + 1,
            r.0.outputs().len() == iter.outputs().len() + 3,
            r.0.states().len() == iter.states().len() + 3,
            forall|i: int|
                #![trigger r.outputs()[i]]
                #![trigger r.states()[i]]
                0 <= i < r.outputs().len() ==> {
                    &&& r.outputs()[i] == r.0.outputs()[i + 3]
                    &&& r.states()[i] == r.0.states()[i + 3]
                },
            r.0.states()[0] == iter.states()[0],
    {
        let mut iter = iter;
        let _ = iter.next();
        let _ = iter.next();
        let _ = iter.next();
        Skip3(iter)
    }
}

impl<T: Iter> Iter for Skip3<T> {
    type Item = T::Item;
    type State = T::State;

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        self.0.outputs().skip(3)
    }

    spec fn states(&self) -> Seq<Self::State> {
        self.0.states().skip(3)
    }

    spec fn inv(&self) -> bool {
        &&& self.0.inv()
        &&& self.0.outputs().len() >= 3
    }

    proof fn inv_well_formed(&self) {
        self.0.inv_well_formed();
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        self.0.next()
    }
}

struct Forget<T>(T, Ghost<nat>);

impl<T: Iter> Forget<T> {
    fn new(iter: T) -> (r: Forget<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            r.states().len() == r.outputs().len() + 1,
            r.0.outputs().len() == iter.outputs().len() + 3,
            r.0.states().len() == iter.states().len() + 3,
            forall|i: int|
                #![trigger r.outputs()[i]]
                #![trigger r.states()[i]]
                0 <= i < r.outputs().len() ==> {
                    &&& r.outputs()[i] == r.0.outputs()[i + 3]
                    &&& r.states()[i] == r.0.states()[i + 3]
                },
            r.0.states()[0] == iter.states()[0],
            r.1 == iter.outputs().len(),
    {
        Forget(iter, Ghost(iter.outputs().len()))
    }
}

impl<T: Iter> Iter for Forget<T> {
    type Item = T::Item;
    type State = (T::State, nat);

    spec fn outputs(&self) -> Seq<Option<Self::Item>> {
        self.0.outputs().skip(self.1@ as int)
    }

    spec fn states(&self) -> Seq<Self::State> {
        self.0.states().skip(self.1@ as int)
    }

    spec fn inv(&self) -> bool {
        &&& self.0.inv()
        &&& self.0.outputs().len() >= 3
    }

    proof fn inv_well_formed(&self) {
        self.0.inv_well_formed();
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        self.0.next()
    }
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

fn test2(v: &MyVec<u8>) {
    let mut iter = v.iter();
    let ghost mut s: Seq<u8> = Seq::empty();
    loop
        invariant_except_break
            s =~= v@.take(iter.outputs().len() as int),
            0 <= iter.outputs().len() <= v@.len(), // should be a for loop auto-invariant
        invariant
            iter.inv(), // should be a for loop auto-invariant
            v@ == iter.vec@, // should be a for loop auto-invariant
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
fn test2_iso_false(v: &MyVec<u8>) {
    let mut iter = v.iter();
    let ghost mut s: Seq<u8> = Seq::empty();
    loop
        invariant
            s =~= v@.take(iter.outputs().len() as int),
            0 <= iter.outputs().len() <= v@.len(), // should be a for loop auto-invariant
            iter.inv(), // should be a for loop auto-invariant
            v@ == iter.vec@, // should be a for loop auto-invariant
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

fn test3(v: &MyVec<u8>)
    requires
        v@.len() >= 6,
{
    let mut iter = Skip3::new(Skip3::new(v.iter()));
    let ghost mut s: Seq<u8> = Seq::empty();
    loop
        invariant_except_break
            s =~= v@.skip(6).take(iter.outputs().len() as int),
            0 <= iter.outputs().len() <= v@.len() - 6,
        invariant
            v@.len() >= 6,
            iter.inv(),
            v@ == iter.0.0.vec@,
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

/*
fn short_test2(v: &MyVec<u8>)
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
    let vi0 = v.iter();
    let ai0 = Skip3::new(vi0);
    let ghost vi3 = ai0.0;

//assert(ai0.0.states()[3] == vi3);
//assert(ai0.0.states()[0] == vi3.states()[0]);
//assert(vi3.states()[0] == vi0);
//assert(ai0.0.states()[0] == vi0);

    let mut bi = Skip3::new(ai0);
    let ghost bi0 = bi;

//assert(bi0.0.states()[0] == ai0);
//assert(bi0.0.states()[0].0.states()[0] == vi0);
    let ghost ai3 = bi0.0;
    let ghost vi6 = bi0.0.0;
//assert(bi0.outputs().len() == 0);
//assert(ai3.outputs().len() == 3);
//assert(ai3.outputs() == ai3.0.outputs().skip(3));
//assert(ai3.outputs().len() == ai3.0.outputs().skip(3).len());
//assert(ai3.0.outputs().len() >= 3);
//assert(ai3.outputs().len() == ai3.0.outputs().len() - 3);
//assert(vi6.outputs().len() == 6);
//assert(vi6.vec == vi0.vec);

    let r = bi.next();
    let ghost bi1 = bi;
    let ghost ai4 = bi1.0;
    let ghost vi7 = bi1.0.0;
//assert(vi7.vec == vi0.vec);
//assert(bi1.outputs().len() == 1);
//assert(ai4.outputs().len() == 4);
//assert(vi7.outputs().len() == 7);
//assert(r == bi1.outputs()[0]);
//assert(r == ai4.outputs()[3]);
//assert(r == vi7.outputs()[6]);

    assert(r == Some(60u8));
}

fn short_test(v: &MyVec<u8>)
    requires
        v.spec_len() == 3,
        v.spec_index(0) == 10,
        v.spec_index(1) == 20,
        v.spec_index(2) == 30,
{
    let vi0 = v.iter();
    let mut si = Skip3::new(vi0);
    let ghost si0 = si;
    let ghost vi1 = si0.0;

/*
    si0.states().len() == si0.outputs().len() + 1,
    si0.inv(),
    vi1.outputs() == iter.outputs().push(vi1.outputs().last()),
    vi1.states() == iter.states().push(vi1.states().last()),
    forall|i: int|
        #![trigger si0.outputs()[i]]
        #![trigger si0.states()[i]]
        0 <= i < si0.outputs().len() ==> si0.states()[i] == Skip3(vi1.states()[i + 1]),
*/

// This makes things work:
//   assert(vi1.states()[0] == vi0);
// The question is why we don't trigger it

assert(vi1.vec.spec_len() == 3);
assume(false);

//assert(si.0.states()[0].vec == &v);
    let r = si.next();
    let ghost si1 = si;
    let ghost vi2 = si1.0;
/*
    si1.states().len() == si1.outputs().len() + 1,
    si1.inv(),
    si1.outputs() =~= si0.outputs().push(r),
    si1.states() =~= si0.states().push(*si1),
    *si0 == si1.states()[si1.outputs().len() - 1],
    forall|i: int|
        #![trigger si1.outputs()[i]]
        #![trigger si1.states()[i]]
        0 <= i < si1.outputs().len() ==> si1.states()[i] == si0.states()[i],
    // TODO: perhaps push should trigger these
    *si1 == si1.states().last(),
    r == si1.outputs().last(),
*/

assert(r == si1.outputs().last());
assert(r == vi2.outputs().drop_first().last());
assert(r == vi2.outputs().drop_first()[0]);
assert(r == Seq::new(vi2.spec_pos@ as nat,
            |i: int| if i < vi2.vec.spec_len() { Some(vi2.vec.spec_index(i)) } else { None },
        )
        .drop_first()[0]
);
assert(vi0.vec.spec_len() == 3);
assert(vi2.vec.spec_len() == 3);
assert(r == Some(vi1.vec.spec_index(1)));

/*

r
= si1.outputs().last(),
= si1.0.outputs().drop_first().last()
= s1.0.outputs().drop_first().last()


*/


    assert(r == Some(20u8));
}

fn test(v: &MyVec<u8>)
    requires
        v.spec_len() == 3,
        v.spec_index(0) == 10,
        v.spec_index(1) == 20,
        v.spec_index(2) == 30,
{
    let mut vi = v.iter();
//assert(vi.pos == 0);
//assert(vi.spec_pos@ == 0);
//assert(vi.outputs().len() == 0);
//assert(vi.states()[0].vec == &v);
    let vi0 = vi.next();
//assert(vi.outputs().len() == 1);
//assert(vi.spec_pos@ == 1);
//assert(vi.pos == 1);
//assert(vi.states()[0].vec == &v);
//assert(vi.states()[1].vec == &v);
    let vi1 = vi.next();
//assert(vi.states()[0].vec == &v);
//assert(vi.states()[1].vec == &v);
//assert(vi.states()[2].vec == &v);
    let vi2 = vi.next();
//assert(vi.states()[0].vec == &v);
//assert(vi.states()[1].vec == &v);
//assert(vi.spec_pos@ == 3);
//assert(vi.states()[2].vec == &v);
//assert(vi.states()[3].vec == &v);
    let vi3 = vi.next();
    assert(vi0 == Some(10u8));
    assert(vi1 == Some(20u8));
    assert(vi2 == Some(30u8));
    assert(vi3.is_none());

    let mut si = Skip3::new(v.iter());
assert(si.outputs().len() == 0);
assert(si.states().len() == 1);
assert(si.0.states()[0].vec == &v);
assert(si.0.states()[1].vec == &v);
assert(si.states()[0].0.vec == &v);
    let si0 = si.next();
assert(si.0.states()[0].vec == &v);
assert(si.0.states()[1].vec == &v);
assert(si.0.states()[2].vec == &v);
assert(si.states()[0].0.vec == &v);
assert(si.states()[1].0.vec == &v);
    let si1 = si.next();
assert(si.0.states()[0].vec == &v);
assert(si.0.states()[1].vec == &v);
assert(si.0.states()[2].vec == &v);
assert(si.0.states()[3].vec == &v);
assert(si.states()[0].0.vec == &v);
assert(si.states()[1].0.vec == &v);
assert(si.states()[2].0.vec == &v);
    let si2 = si.next();
assert(si.0.states()[0].vec == &v);
assert(si.0.states()[1].vec == &v);
assert(si.0.states()[2].vec == &v);
assert(si.0.states()[3].vec == &v);
assert(si.0.states()[4].vec == &v);
assert(si.states()[0].0.vec == &v);
assert(si.states()[1].0.vec == &v);
assert(si.states()[2].0.vec == &v);
assert(si.states()[3].0.vec == &v);
    assert(si0 == Some(20u8));
    assert(si1 == Some(30u8));
    assert(si2.is_none());

    let mut si = Skip3::new(Skip3::new(v.iter()));
assert(si.0.0.states()[0].vec == &v);
assert(si.0.0.states()[1].vec == &v);
assert(si.0.0.states()[2].vec == &v);
assert(si.0.states()[0].0.vec == &v);
assert(si.0.states()[1].0.vec == &v);
assert(si.states()[0].0.0.vec == &v);
    let si0 = si.next();
    let si1 = si.next();
    assert(si0 == Some(30u8));
    assert(si1.is_none());

/*
    let mut ei = EachTwice::new(Skip3::new(v.iter()));
    assert(ei.len() == Some(4int));
    let ei0 = ei.next();
    let ei1 = ei.next();
    let ei2 = ei.next();
    let ei3 = ei.next();
    let ei4 = ei.next();
    assert(ei0 == Some(20u8));
    assert(ei1 == Some(20u8));
    assert(ei2 == Some(30u8));
    assert(ei3 == Some(30u8));
    assert(ei4.is_none());

    let mut ei = EachTwice::new(RandomByteIter::new());
    let ei0 = ei.next();
    let ei1 = ei.next();
    let ei2 = ei.next();
    let ei3 = ei.next();
    let ei4 = ei.next();
    assert(ei0 == ei1);
    assert(ei2 == ei3);
    assert(ei4.is_some());
*/
}

struct EachTwice<T: Iter> {
    iter: T,
    copy: Option<Option<T::Item>>,
}

impl<T: Iter> EachTwice<T> where T::Item: Copy {
    fn new(iter: T) -> (r: EachTwice<T>)
        requires
            iter.inv(),
        ensures
            r.inv(),
            r.pos() == iter.pos() * 2,
            iter.len().is_none() ==> r.len().is_none(),
            iter.len() matches Some(l) ==> r.len() == { Some(2 * l) },
            forall|i: int| r.index(i) == iter.index(i / 2),
    {
        EachTwice { iter, copy: None }
    }
}

impl<T: Iter> Iter for EachTwice<T> where T::Item: Copy {
    type Item = T::Item;

    spec fn pos(&self) -> int {
        2 * self.iter.pos() - if self.copy.is_none() { 0int } else { 1int }
    }

    #[verifier::prophetic]
    spec fn index(&self, i: int) -> Option<Self::Item> {
        self.iter.index(i / 2)
    }

    #[verifier::prophetic]
    spec fn len(&self) -> Option<int> {
        if let Some(l) = self.iter.len() {
            Some(2 * l)
        } else {
            None
        }
    }

    spec fn inv(&self) -> bool {
        &&& self.iter.inv()
        &&& self.copy matches Some(copy) ==> self.index(self.pos()) == copy
    }

    fn next(&mut self) -> (r: Option<Self::Item>) {
        if let Some(copy) = self.copy {
            self.copy = None;
            copy
        } else {
            let r = self.iter.next();
            self.copy = Some(r);
            r
        }
    }
}
*/

} // verus!
