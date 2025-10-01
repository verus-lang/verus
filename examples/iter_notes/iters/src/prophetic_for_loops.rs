use std::{iter::{self, Skip}, path::Iter};

use vstd::prelude::*;

verus!{

pub trait Iterator {
    type Item;

    /// This iterator obeys the specifications below on `next`
    spec fn obeys_iter_laws(&self) -> bool;

    /// Seq that will be returned
    #[verifier::prophetic]
    spec fn seq(&self) -> Seq<Self::Item>;

    /// Does this complete with a `None` after the above sequence?
    /// (As opposed to hanging indefinitely on a `next()` call)
    #[verifier::prophetic]
    spec fn completes(&self) -> bool;

    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.obeys_iter_laws() == old(self).obeys_iter_laws(),
            self.obeys_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_iter_laws() ==> 
            ({
                if old(self).seq().len() > 0 {
                    &&& self.seq() == old(self).seq().drop_first()
                    &&& ret == Some(old(self).seq()[0])
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            }),
    ;

    /******* Mechanisms that support ergonomic `for` loops *********/

    type Decrease;

    /// Optional invariant about the iterator.
    /// May be disabled with #[verifier::no_auto_loop_invariant]
    /// If enabled, always true before and after each loop iteration.
    /// (When Verus can infer a spec initial value based on the
    ///  exec value used to create the iterator, it passes the expression
    ///  as `Some(expression)`. This can enable a much stronger invariant.
    spec fn loop_invariant(&self, init: Option<&Self>) -> bool;

    /// True upon loop exit
    spec fn loop_ensures(&self) -> bool;

    /// Value used by default for decreases clause when no explicit decreases clause is provided
    /// (the user can override this with an explicit decreases clause).
    /// If there's no appropriate decrease, this can return None,
    /// and the user will have to provide an explicit decreases clause.
    spec fn decrease(&self) -> Option<Self::Decrease>;

    // REVIEW: BP: With the prophetic encoding, I don't think we need this;
    //             There's a generic peek next based on trying to look at seq().first().
    // If there will be Some next value, and we can make a useful guess as to what the next value
    // will be, return Some of it.
    // Otherwise, return None.
    // TODO: in the long term, we could have VIR insert an assertion (or warning)
    // that peek_next returns non-null if it is used in the invariants.
    // (this will take a little bit of engineering since the syntax macro blindly inserts
    // let bindings using peek_next, even if they aren't needed, and we only learn
    // what is actually needed later in VIR.)
    //spec fn peek_next(&self) -> Option<Self::Item>;

}

pub trait DoubleEndedIterator : Iterator {

    fn next_back(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.obeys_iter_laws() == old(self).obeys_iter_laws(),
            self.obeys_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_iter_laws() ==> 
            ({
                if old(self).seq().len() > 0 {
                    self.seq() == old(self).seq().drop_last()
                        && ret == Some(old(self).seq().last())
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            });

}

/* vec iterator */

pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
    j: usize,
}

impl <'a, T> VecIterator<'a, T> {
    pub closed spec fn front(self) -> usize {
        self.i
    }
    
    pub closed spec fn back(self) -> usize {
        self.j
    }

    pub closed spec fn elts(self) -> Seq<T> {
        self.v@
    }

    #[verifier::type_invariant]
    pub closed spec fn vec_iterator_type_inv(self) -> bool {
        self.i <= self.j <= self.v.len()
    }
}

pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures 
        iter.seq() == v@.map(|i, v| &v),
        iter.vec_iterator_type_inv(),
        iter.front() == 0,
        iter.back() == v.len(),
        iter.elts() == v@,
{
    VecIterator { v: v, i: 0, j: v.len() }
}

impl<'a, T> Iterator for VecIterator<'a, T> {
    type Item = &'a T;

    open spec fn obeys_iter_laws(&self) -> bool {
        true
    }

    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.v@.subrange(self.i as int, self.j as int).map(|i, v| &v)
    }

    closed spec fn completes(&self) -> bool {
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) 
        ensures
            self.back() == old(self).back(),
            if old(self).front() < old(self).back() {
                self.front() == old(self).front() + 1
            } else {
                self.front() == old(self).front()
            },
            self.elts() == old(self).elts(),
    {
        proof { use_type_invariant(&*self); }
        if self.i < self.j {
            let i = self.i;
            self.i = self.i + 1;
            let ret = Some(&self.v[i]);
            return ret;
        } else {
            return None;
        }
    }

    type Decrease = int;

    open spec fn loop_invariant(&self, init: Option<&Self>) -> bool {
        &&& self.vec_iterator_type_inv()
        &&& init matches Some(init) ==> {
            &&& init.front() == 0 
            &&& init.back() == self.elts().len() 
            &&& init.elts() == self.elts()
            &&& self.front() >= init.front()
            &&& self.back() <= init.back()
        }
    }

    open spec fn loop_ensures(&self) -> bool {
        self.front() == self.back()
    }

    open spec fn decrease(&self) -> Option<Self::Decrease> {
        Some((self.back() - self.front()) as int)
    }

    // open spec fn peek_next(&self) -> Option<Self::Item> {
    //     if self.front() < self.back() {
    //         Some(&self.elts()[self.front() as int])
    //     } else {
    //         None
    //     }
    // }
}

impl<'a, T> DoubleEndedIterator for VecIterator<'a, T> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.vec_iterator_type_inv());
        //proof { use_type_invariant(&*self); }
        if self.i < self.j {
            self.j = self.j - 1;
            return Some(&self.v[self.j]);
        } else {
            return None;
        }
    }
}

/* proph util (this should be implementable) */

pub trait Predicate<T> {
    #[verifier::prophetic]
    spec fn pred(&self, i: int, t: T) -> bool;
}

#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::accept_recursive_types(Pred)]
pub tracked struct ProphSeq<T, Pred> { t: T, pred: Pred }

impl<T, Pred> ProphSeq<T, Pred>
    where Pred: Predicate<T>
{
    pub uninterp spec fn pred(&self) -> Pred;
    pub uninterp spec fn proph_elem(&self, i: int) -> Option<T>;
    pub uninterp spec fn has_resolved(&self, i: int) -> bool;

    pub axiom fn new(pred: Pred) -> (tracked s: Self)
        ensures
            s.pred() == pred,
            forall |i| !s.has_resolved(i);


    pub axiom fn proph_elem_meets_pred(tracked &self)
        ensures forall |i: int| (match #[trigger] self.proph_elem(i) {
            Some(p) => self.pred().pred(i, p),
            None => true,
        });

    pub axiom fn resolve(tracked &mut self, i: int, t: T)
        requires
            !old(self).has_resolved(i),
            old(self).pred().pred(i, t),
        ensures
            self.pred() == old(self).pred(),
            forall |j| self.proph_elem(j) == old(self).proph_elem(j),
            forall |j| i != j ==> self.has_resolved(j) == old(self).has_resolved(j),
            self.proph_elem(i) == Some(t);
}


/* map iterator */

/*
ghost struct MapIteratorPred<Iter, F> {
    iter: Iter,
    f: F,
}

impl<Item, Iter, F> Predicate<Item> for MapIteratorPred<Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    #[verifier::prophetic]
    closed spec fn pred(&self, i: int, t: Item) -> bool {
        call_ensures(self.f, (self.iter.seq()[i],), t)
    }
}

pub struct MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    f: F,
    iter: Iter,

    prophs: Tracked<ProphSeq<Item, MapIteratorPred<Iter, F>>>,
    idx: Ghost<int>,
}

impl<Item, Iter, F> MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    pub closed spec fn inner(self) -> Iter {
        self.iter
    }

    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    closed spec fn map_iterator_type_inv(self) -> bool {
        0 <= self.idx@ <= self.prophs@.pred().iter.seq().len()
          && self.iter.seq() =~= self.prophs@.pred().iter.seq().skip(self.idx@)
          && self.prophs@.pred().f == self.f
          && (forall |i| #![auto] 0 <= i < self.iter.seq().len() ==> call_requires(self.f, (self.iter.seq()[i], )))
          && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> !self.prophs@.has_resolved(i))
          && self.iter.obeys_iter_laws()
    }

    fn new(iter: Iter, f: F) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
            forall |i| #![auto] 0 <= i < iter.seq().len() ==>
                call_requires(f, (iter.seq()[i], ))
        ensures
            s.seq().len() <= iter.seq().len(),
            forall |i| #![auto] 0 <= i < s.seq().len() ==>
                call_ensures(f, (iter.seq()[i],), s.seq()[i]),
            s.completes() ==> iter.completes() && s.seq().len() == iter.seq().len(),
    {
        let s = Self {
            f: f,
            iter: iter,
            prophs: Tracked(ProphSeq::new(MapIteratorPred {
                iter: iter,
                f: f,
            })),
            idx: Ghost(0),
        };
        
        assert(s.map_iterator_type_inv());
        proof {
            s.prophs.borrow().proph_elem_meets_pred();
            // PAPER CUT: can't call lemma with prophetic arg
            broadcast use unwrap_up_to_first_none_len_le; //(s.seq_of_options());
            broadcast use unwrap_up_to_first_none_len_le_values;
        }
        s
    }

    #[verifier::prophetic]
    spec fn seq_of_options(&self) -> Seq<Option<Item>> {
        Seq::new(self.iter.seq().len(), |i| {
            self.prophs@.proph_elem(self.idx@ + i)
        })
    }
}

spec fn unwrap_up_to_first_none<T>(seq: Seq<Option<T>>) -> Seq<T>
    decreases seq.len()
{
    if seq.len() == 0 {
        seq![]
    } else if seq[0].is_some() {
        seq![seq[0].unwrap()] + unwrap_up_to_first_none(seq.drop_first())
    } else {
        seq![]
    }
}

broadcast proof fn unwrap_up_to_first_none_len_le<T>(seq: Seq<Option<T>>)
    ensures #[trigger] unwrap_up_to_first_none(seq).len() <= seq.len(),
        (forall |i| 0 <= i < seq.len() ==> seq[i].is_some()) ==>
            unwrap_up_to_first_none(seq).len() == seq.len(),
    decreases seq.len()
{
    if seq.len() != 0 && seq[0].is_some() {
        unwrap_up_to_first_none_len_le(seq.drop_first());
    }
}

broadcast proof fn unwrap_up_to_first_none_len_le_values<T>(seq: Seq<Option<T>>, i: int)
    requires 0 <= i < unwrap_up_to_first_none(seq).len()
    ensures
        i < seq.len(),
        seq[i].is_some(),
        #[trigger] unwrap_up_to_first_none(seq)[i] == seq[i].unwrap(),
    decreases seq.len()
{
    if i > 0 {
        unwrap_up_to_first_none_len_le_values(seq.drop_first(), i-1);
    }
}
impl<Item, Iter, F> Iterator for MapIterator<Item, Iter, F>
    where
        Iter: Iterator,
        F: Fn(Iter::Item) -> Item
{
    type Item = Item;

    open spec fn obeys_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        unwrap_up_to_first_none(self.seq_of_options())
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
          && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> self.prophs@.proph_elem(i).is_some())
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) 
        ensures
            self.inner() == old(self).inner(),
    {
        assume(self.map_iterator_type_inv());

        match self.iter.next() {
            None => {
                assert(self.map_iterator_type_inv());
                return None;
            }
            Some(elem) => {
                let output = (self.f)(elem);
                proof {
                    self.prophs.borrow_mut().resolve(self.idx@, output);
                    self.idx@ = self.idx@ + 1;
                }

                assert(self.seq_of_options() == old(self).seq_of_options().drop_first());
                assert(self.map_iterator_type_inv());
                return Some(output);
            }
        }
    }

    type Decrease = Iter::Decrease;

    open spec fn loop_invariant(&self, init: Option<&Self>) -> bool {
       // TODO: We shouldn't need this when the type invariant is working
       //&&& self.map_iterator_type_inv()
       &&& init matches Some(init) ==>
                self.inner().loop_invariant(Some(&init.inner()))
    }

    open spec fn loop_ensures(&self) -> bool {
        self.inner().loop_ensures()
    }

    open spec fn decrease(&self) -> Option<Self::Decrease> {
        self.inner().decrease()
    }

    open spec fn peek_next(&self) -> Option<Self::Item> {
        if self.seq().len() > 0 {
            Some(self.seq().first())
        } else {
            None
        }
        // match self.inner().peek_next() {
        //     Some(next) => {
        //         self.iter.peek_next()
        //     },
        //     None => None,
        // }
    }

}


// take

struct TakeIterator<Iter: Iterator> {
    iter: Iter,
    count_remaining: usize,
}

impl<Iter: Iterator> TakeIterator<Iter> {
    //#[verifier::type_invariant] // fake this (via assert/assume below) due to limitations:
    //  With this as a type invariantVerus won't let us call self.iter.next() unless it's marked no_unwind
    #[verifier::prophetic]
    closed spec fn take_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }

    fn new(iter: Iter, count: usize) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == (if iter.seq().len() < count { iter.seq() } else { iter.seq().take(count as int) }),
            s.completes() <==> iter.completes() || iter.seq().len() >= count,
            s.obeys_iter_laws(),
    {
        let t= TakeIterator {
            iter: iter,
            count_remaining: count,
        };
        assert(t.take_inv());
        t
    }
}

impl<Iter: Iterator> Iterator for TakeIterator<Iter> {
    type Item = Iter::Item;

    open spec fn obeys_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        if self.iter.seq().len() < self.count_remaining { self.iter.seq() } else { self.iter.seq().take(self.count_remaining as int) }
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes() || self.iter.seq().len() >= self.count_remaining
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.take_inv());
        if self.count_remaining == 0 {
            None
        } else {
            self.count_remaining = self.count_remaining - 1;
            self.iter.next()
        }
    }
}

// skip

struct SkipIterator<Iter: Iterator> {
    iter: Iter,
}

impl<Iter: Iterator> SkipIterator<Iter> {
    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    closed spec fn skip_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }
}

impl<Iter: Iterator> SkipIterator<Iter> {
    fn new(iter: Iter, count: usize) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == (if iter.seq().len() < count { seq![] } else { iter.seq().skip(count as int) }),
            s.completes() <==> iter.completes(),
            iter.seq().len() < count ==> iter.completes(),
    {
        let mut i = 0;
        let mut iter0 = iter;
        while i < count
            invariant
                i <= count,
                iter0.obeys_iter_laws(),
                iter0.seq() == (if iter.seq().len() < i { seq![] } else { iter.seq().skip(i as int) }),
                iter0.completes() <==> iter.completes(),
                iter.seq().len() < i ==> iter.completes(),
            decreases count - i,
        {
            iter0.next();
            i += 1;
        }
        
        let s = SkipIterator {
            iter: iter0,
        };
        assert(s.skip_inv());
        s
    }
}

impl<Iter: Iterator> Iterator for SkipIterator<Iter> {
    type Item = Iter::Item;

    open spec fn obeys_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.iter.seq()
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.skip_inv());
        self.iter.next()
    }
}

// reverse iterator
struct ReverseIterator<Iter: Iterator> {
    iter: Iter,
}

impl<Iter: Iterator> ReverseIterator<Iter> {
    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    closed spec fn reverse_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }
}

impl<Iter: Iterator + DoubleEndedIterator> ReverseIterator<Iter> {
    fn new(iter: Iter) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == iter.seq().reverse(),
            s.completes() <==> iter.completes(),
    {
        let r = ReverseIterator {
            iter: iter,
        };
        assert(r.reverse_inv());
        r
    }
}

impl<Iter: Iterator + DoubleEndedIterator> Iterator for ReverseIterator<Iter> {
    type Item = Iter::Item;

    open spec fn obeys_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.iter.seq().reverse()
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        self.iter.next_back()
    }
}

impl<Iter: Iterator + DoubleEndedIterator> DoubleEndedIterator for ReverseIterator<Iter> {
    fn next_back(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.reverse_inv());
        self.iter.next()
    }
}

// collect

#[verifier::exec_allows_no_decreases_clause]
fn collect_to_vec<Iter: Iterator>(iter: Iter) -> (s: Vec<Iter::Item>)
    requires
        iter.obeys_iter_laws(),
    ensures s@ == iter.seq(),
        iter.completes(),
{
    let mut iter0 = iter;
    let mut v = vec![];
    loop
        invariant
            iter0.obeys_iter_laws(),
            v@ + iter0.seq() =~= iter.seq(),
            iter.completes() == iter0.completes(),
    {
        match iter0.next() {
            Some(elem) => {
                v.push(elem);
            }
            None => {
                return v;
            }
        }
    }
}

// examples

fn test() {
    let f = |i: &u8| -> (out: u8)
        requires i < 255,
        ensures out == i + 1,
        {
            *i + 1
        };
    let g = |i: u8| -> (out: u8)
        requires i >= 3
        ensures out == i - 3,
        {
            i - 3
        };

    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];

    let iter = vec_iter(&v);
    let iter = ReverseIterator::new(iter); // 6 5 4 3 2 1
    let iter = MapIterator::new(iter, f);  // 7 6 5 4 3 2
    let iter = TakeIterator::new(iter, 5); // 7 6 5 4 3
    let iter = MapIterator::new(iter, g);  // 4 3 2 1 0
    let iter = SkipIterator::new(iter, 1); // 3 2 1 0
    let iter = TakeIterator::new(iter, 3); // 3 2 1
    let w = collect_to_vec(iter);

    assert(w@ === seq![3, 2, 1]);
}

#[verifier::exec_allows_no_decreases_clause]
#[verifier::loop_isolation(false)]
fn test_loop() {
    let f = |i: &u8| -> (out: u8)
        requires i < 255,
        ensures out == i + 1,
        {
            *i + 1
        };
    let g = |i: u8| -> (out: u8)
        requires i >= 3
        ensures out == i - 3,
        {
            i - 3
        };

    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];

    let iter = vec_iter(&v);
    let iter = ReverseIterator::new(iter); // 6 5 4 3 2 1
    let iter = MapIterator::new(iter, f);  // 7 6 5 4 3 2
    let iter = TakeIterator::new(iter, 5); // 7 6 5 4 3
    let iter = MapIterator::new(iter, g);  // 4 3 2 1 0
    let iter = SkipIterator::new(iter, 1); // 3 2 1 0
    let iter = TakeIterator::new(iter, 3); // 3 2 1

    // for elem in iter {
    //    assert(1 <= elem <= 3);
    // }

    let mut iter = iter;
    let ghost iter_snapshot = iter;
    let ghost mut idx = 0;
    loop
        invariant
            0 <= idx <= iter_snapshot.seq().len(),
            iter.seq() =~= iter_snapshot.seq().skip(idx)
    {
        match iter.next() {
            None => {
                break;
            }
            Some(elem) => {
                /* body */
                assert(1 <= elem <= 3);
            }
        }

        proof { idx = idx + 1; }
    }
}

fn all_true<'a, I: Iterator<Item=&'a bool>>(iter: &mut I) -> (r: bool)
    requires
        old(iter).completes(),
    ensures
        r == forall |i| 0 <= i < old(iter).seq().len() ==> *#[trigger]old(iter).seq()[i]
{
    // TODO
    assume(false);
    true
}

fn all_true_caller(v: &Vec<bool>)
    requires
        v@.len() == 10,
{
    let mut iter: VecIterator<bool> = vec_iter(v);
    let ghost iter_snapshot = iter;
    assert(iter.seq() == v@.map(|i, v| &v));
    let b = all_true(&mut iter);
    proof {
        if b {
            // Note: We have to mention the iter_snapshot-based trigger to get the "real"
            //       assertion on the following line to go through
            assert(forall |i| 0 <= i < v@.len() ==> v@[i] == *iter_snapshot.seq()[i]);
            assert(forall |i| 0 <= i < v@.len() ==> v@[i]);
        }
    }
}
*/
fn for_loop_test() {

    let v: Vec<u8> = vec![1, 2, 3, 4, 5, 6];
    let mut w: Vec<u8> = vec![];

    let i = vec_iter(&v);
    assert(i.loop_invariant(Some(&i)));

    let mut count: u128 = 0;
    // Verus will desugar this: 
    //
    // for x in y: v 
    //     invariant
    //         w@ + y.seq().map_values(|r:&u8| *r) == v@
    // {
    //     w.push(x);
    // }
    //
    // Into:
    #[allow(non_snake_case)]
    let VERUS_iter = v;
    #[allow(non_snake_case)]
    let VERUS_loop_result = match vec_iter(&VERUS_iter) {
        mut y => {
            let ghost VERUS_snapshot = y;
            //let ghost mut y = VERUS_exec_iter;
            loop
                invariant
                    y.loop_invariant(Some(&VERUS_snapshot)),
                    ({ 
                      // Grab the next val for (possible) use in inv
                      let x = if y.seq().len() > 0 { y.seq().first() } else { arbitrary() };
                      //let x = y.peek_next().unwrap_or(arbitrary());

                      // inv
                      w@ + y.seq().map_values(|r:&u8| *r) == v@ &&
                      count == w.len() <= u64::MAX
                    }),
                ensures
                    y.loop_ensures(),
                decreases
                    y.decrease().unwrap_or(arbitrary()),
            {
                #[allow(non_snake_case)]
                let mut VERUS_loop_next;
                match y.next() {
                    Some(VERUS_loop_val) => VERUS_loop_next = VERUS_loop_val,
                    None => {
                        break
                    }
                }
                let x = VERUS_loop_next;
                let () = {
                    // body
                    w.push(*x);
                    count += 1;
                };
            }
        }
    };

    // Make sure our invariant was useful
    assert(w@ == v@);
    assert(count == v.len());
}
}

