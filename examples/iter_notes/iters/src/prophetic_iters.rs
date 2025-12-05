use std::{io::Take, iter::{self, Skip}, path::Iter};
use vstd::prelude::*;

verus!{

pub mod decreases_fix {

use vstd::prelude::*;

pub uninterp spec fn does_decrease<A>(from: A, to: A) -> bool;

pub broadcast axiom fn does_decrease_decreases<A>(from: A, to: A)
    ensures
        #[trigger] does_decrease(from, to) <==> decreases_to!(from => to);

pub broadcast axiom fn does_decrease_option<T>(from: Option<T>, to: Option<T>)
    ensures
        #[trigger] does_decrease(from, to) <==>
            (from matches Some(f) && (to is None || (to matches Some(t) && does_decrease(f, t))))
;

pub broadcast axiom fn does_decrease_int(from: int, to: int)
    ensures
        #[trigger] does_decrease(from, to) <==> 0 <= to < from,
;

pub broadcast axiom fn does_decrease_nat(from: nat, to: nat)
    ensures
        #[trigger] does_decrease(from, to) <==> 0 <= to < from,
;

pub broadcast axiom fn does_decrease_u32(from: u32, to: u32)
    ensures
        #[trigger] does_decrease(from, to) <==> 0 <= to < from,
;

pub broadcast axiom fn does_decrease_u64(from: u64, to: u64)
    ensures
        #[trigger] does_decrease(from, to) <==> 0 <= to < from,
;

pub broadcast axiom fn does_decrease_usize(from: usize, to: usize)
    ensures
        #[trigger] does_decrease(from, to) <==> 0 <= to < from,
;

pub broadcast group group_decrease_axioms {
    does_decrease_decreases,
    does_decrease_option,
    does_decrease_int,
    does_decrease_nat,
    does_decrease_u32,
    does_decrease_u64,
    does_decrease_usize,
}

}


pub mod iterator_traits {

use vstd::prelude::*;
use super::decreases_fix::*;

broadcast use group_decrease_axioms;


// PAPER CUT: When a proof fails, you can't mention prophetic functions 
//            as part of proof debugging.  E.g., you can't write:
//            proof { if prophetic_fn() { assert(P) } else { assert(Q) } }

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

    // Invariant relating the iterator to its initial value.
    // When the analysis can infer a spec initial value, the analysis 
    // places the value in init
    spec fn initial_value_inv(&self, init: Option<&Self>) -> bool;

    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.obeys_iter_laws() == old(self).obeys_iter_laws(),
            self.obeys_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_iter_laws() ==> (old(self).decrease() is Some <==> self.decrease() is Some),
            self.obeys_iter_laws() ==> 
            ({
                if old(self).seq().len() > 0 {
                    &&& self.seq() == old(self).seq().drop_first()
                    &&& ret == Some(old(self).seq()[0])
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            }),
            self.obeys_iter_laws() && old(self).seq().len() > 0 && self.decrease() is Some ==> 
                does_decrease(old(self).decrease(), self.decrease()),
    ;

    /******* Mechanisms that support ergonomic `for` loops *********/

    type Decrease;

    /// Value used by default for decreases clause when no explicit decreases clause is provided
    /// (the user can override this with an explicit decreases clause).
    /// If there's no appropriate decrease, this can return None,
    /// and the user will have to provide an explicit decreases clause.
    spec fn decrease(&self) -> Option<Self::Decrease>;
}

pub trait DoubleEndedIterator : Iterator {

    fn next_back(&mut self) -> (ret: Option<Self::Item>)
        ensures
            self.obeys_iter_laws() == old(self).obeys_iter_laws(),
            self.obeys_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_iter_laws() ==> (old(self).decrease() is Some <==> self.decrease() is Some),
            self.obeys_iter_laws() ==> 
            ({
                if old(self).seq().len() > 0 {
                    self.seq() == old(self).seq().drop_last()
                        && ret == Some(old(self).seq().last())
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            }),
            self.obeys_iter_laws() && old(self).seq().len() > 0 && self.decrease() is Some ==> 
                does_decrease(old(self).decrease(), self.decrease()),
    ;

}

/* vec iterator */

pub struct VecIterator<'a, T> {
    v: &'a Vec<T>,
    i: usize,
    j: usize,
}

impl <'a, T> VecIterator<'a, T> {
    pub closed spec fn new(v: &'a Vec<T>) -> Self {
        VecIterator { v, i: 0, j: v.len() }
    }

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
        &&& self.i <= self.j <= self.v.len()
        &&& self.front() <= self.back() <= self.elts().len()
    }
}

pub open spec fn vec_iter_spec<'a, T>(v: &'a Vec<T>) -> VecIterator<'a, T> {
    VecIterator::new(v)
}

#[verifier::when_used_as_spec(vec_iter_spec)]
pub fn vec_iter<'a, T>(v: &'a Vec<T>) -> (iter: VecIterator<'a, T>)
    ensures 
        iter.seq() == v@.map(|i, v| &v),
        iter.vec_iterator_type_inv(),
        iter.front() == 0,
        iter.back() == v.len(),
        iter.elts() == v@,
        iter.decrease() is Some,
        iter.initial_value_inv(Some(&vec_iter_spec(v))),
{
    let i = VecIterator { v: v, i: 0, j: v.len() };
    assert(i.elts() == i.seq().map_values(|v: &T| *v));     // OBSERVE
    i
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

    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        &&& self.elts() == self.seq().map_values(|v: &T| *v)
        &&& init matches Some(v) && v.elts() == self.elts()
    }

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

    type Decrease = usize;

    closed spec fn decrease(&self) -> Option<Self::Decrease> {
        Some((self.back() - self.front()) as usize)
    }
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
            self.has_resolved(i),       // REVIEW: BP: I added this.  Seems like it's the point of calling `resolve`
            self.proph_elem(i) == Some(t);
}


/* map iterator */

pub ghost struct MapIteratorPred<Iter, F> {
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

    pub closed spec fn the_prophs(self) -> ProphSeq<Item, MapIteratorPred<Iter, F>> {
        self.prophs@
    }

    pub closed spec fn count(self) -> nat {
        self.idx@ as nat
    }

    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    pub closed spec fn map_iterator_type_inv(self) -> bool {
        0 <= self.idx@ <= self.prophs@.pred().iter.seq().len()
          && self.iter.seq() =~= self.prophs@.pred().iter.seq().skip(self.idx@)
          && self.prophs@.pred().f == self.f
          && (forall |i| #![auto] 0 <= i < self.iter.seq().len() ==> call_requires(self.f, (self.iter.seq()[i], )))
          && (forall |i: int| self.idx@ <= i < self.idx@ + self.iter.seq().len() ==> !self.prophs@.has_resolved(i))
          && self.iter.obeys_iter_laws()
          // New
          // Not clear if this is useful, since seq() only talks about the values of
          // prophs that are >= self.idx
          && (forall |i: int|
                #![trigger self.prophs@.has_resolved(i)]
                #![trigger self.prophs@.proph_elem(i)]
                0 <= i < self.idx@ ==> self.prophs@.has_resolved(i) && self.prophs@.proph_elem(i).is_some())
    }

    pub fn new(iter: Iter, f: F) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
            forall |i| #![auto] 0 <= i < iter.seq().len() ==>
                call_requires(f, (iter.seq()[i], ))
        ensures
            s.seq().len() <= iter.seq().len(),
            forall |i| #![auto] 0 <= i < s.seq().len() ==>
                call_ensures(f, (iter.seq()[i],), s.seq()[i]),
            s.completes() ==> iter.completes() && s.seq().len() == iter.seq().len(),
            s.count() == 0,
            s.inner() == iter,
            s.decrease() is Some == iter.decrease() is Some,
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

pub closed spec fn unwrap_up_to_first_none<T>(seq: Seq<Option<T>>) -> Seq<T>
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

pub broadcast proof fn unwrap_up_to_first_none_len_le<T>(seq: Seq<Option<T>>)
    ensures #[trigger] unwrap_up_to_first_none(seq).len() <= seq.len(),
        (forall |i| 0 <= i < seq.len() ==> seq[i].is_some()) ==>
            unwrap_up_to_first_none(seq).len() == seq.len(),
    decreases seq.len()
{
    if seq.len() != 0 && seq[0].is_some() {
        unwrap_up_to_first_none_len_le(seq.drop_first());
    }
}

pub broadcast proof fn unwrap_up_to_first_none_len_le_values<T>(seq: Seq<Option<T>>, i: int)
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

    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        // TODO
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) 
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

    closed spec fn decrease(&self) -> Option<Self::Decrease> {
        self.inner().decrease()
    }

}


// take

pub struct TakeIterator<Iter: Iterator> {
    iter: Iter,
    count_remaining: usize,
}

impl<Iter: Iterator> TakeIterator<Iter> {
    pub closed spec fn inner(self) -> Iter {
        self.iter
    }

    pub closed spec fn count(self) -> usize {
        self.count_remaining
    }

    //#[verifier::type_invariant] // fake this (via assert/assume below) due to limitations:
    //  With this as a type invariantVerus won't let us call self.iter.next() unless it's marked no_unwind
    #[verifier::prophetic]
    pub closed spec fn take_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }

    pub fn new(iter: Iter, count: usize) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == (if iter.seq().len() < count { iter.seq() } else { iter.seq().take(count as int) }),
            s.completes() <==> iter.completes() || iter.seq().len() >= count,
            s.obeys_iter_laws(),
            s.inner() == iter,
            s.count() == count,
            s.decrease() is Some,
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

    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        // TODO
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) 
    {
        assume(self.take_inv());
        if self.count_remaining == 0 {
            None
        } else {
            self.count_remaining = self.count_remaining - 1;
            self.iter.next()
        }
    }

    type Decrease = usize;

    closed spec fn decrease(&self) -> Option<Self::Decrease> {
        Some(self.count())
    }
}


// skip

pub struct SkipIterator<Iter: Iterator> {
    iter: Iter,
}

impl<Iter: Iterator> SkipIterator<Iter> {
    pub closed spec fn inner(self) -> Iter {
        self.iter
    }

    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    pub closed spec fn skip_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }
}

impl<Iter: Iterator> SkipIterator<Iter> {
    pub fn new(iter: Iter, count: usize) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == (if iter.seq().len() < count { seq![] } else { iter.seq().skip(count as int) }),
            s.completes() <==> iter.completes(),
            iter.seq().len() < count ==> iter.completes(),
            s.decrease() is Some == iter.decrease() is Some,
    {
        let mut i = 0;
        let ghost iter_snapshot = iter;
        let mut iter0 = iter;
        while i < count
            invariant
                i <= count,
                iter0.obeys_iter_laws(),
                iter0.decrease() is Some == iter_snapshot.decrease() is Some,
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
    
    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        // TODO
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.skip_inv());
        self.iter.next()
    }

    type Decrease = Iter::Decrease;

    closed spec fn decrease(&self) -> Option<Self::Decrease> {
        self.inner().decrease()
    }


}

// reverse iterator
pub struct ReverseIterator<Iter: Iterator> {
    iter: Iter,
}

impl<Iter: Iterator> ReverseIterator<Iter> {
    //#[verifier::type_invariant] // fake this due to limitations
    #[verifier::prophetic]
    pub closed spec fn reverse_inv(self) -> bool {
        self.iter.obeys_iter_laws()
    }

    pub closed spec fn inner(self) -> Iter {
        self.iter
    }
}

impl<Iter: Iterator + DoubleEndedIterator> ReverseIterator<Iter> {
    pub fn new(iter: Iter) -> (s: Self)
        requires
            iter.obeys_iter_laws(),
        ensures
            s.seq() == iter.seq().reverse(),
            s.completes() <==> iter.completes(),
            s.decrease() is Some == iter.decrease() is Some
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
        self.inner().obeys_iter_laws()
    }

    #[verifier::prophetic]
    closed spec fn seq(&self) -> Seq<Self::Item> {
        self.iter.seq().reverse()
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        self.iter.completes()
    }

    open spec fn initial_value_inv(&self, init: Option<&Self>) -> bool {
        // TODO
        true
    }

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        assume(self.reverse_inv());
        self.iter.next_back()
    }

    type Decrease = Iter::Decrease;

    closed spec fn decrease(&self) -> Option<Self::Decrease> {
        self.inner().decrease()
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
pub fn collect_to_vec<Iter: Iterator>(iter: Iter) -> (s: Vec<Iter::Item>)
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

/// REVIEW: Despite the name, VerusForLoopIterator doesn't implement Iterator.
///         What would be a better name?
pub struct VerusForLoopIterator<'a, I: Iterator> {
    pub index: Ghost<int>,
    pub snapshot: Ghost<I>,
    pub init: Ghost<Option<&'a I>>,
    pub iter: I 
}
impl <'a, I: Iterator> VerusForLoopIterator<'a, I> {
    #[verifier::prophetic]
    pub open spec fn seq(self) -> Seq<I::Item> {
        self.snapshot@.seq()
    }

    /// These properties help maintain the properties in wf,
    /// but they don't need to be exposed to the client 
    #[verifier::prophetic]
    pub closed spec fn wf_inner(self) -> bool {
        &&& self.iter.seq().len() == self.seq().len() - self.index@
        &&& forall |i| 0 <= i < self.iter.seq().len() ==> #[trigger] self.iter.seq()[i] == self.seq()[self.index@ + i]
        &&& self.iter.completes() ==> self.snapshot@.completes()
    }

    /// These properties are needed for the client code to verify
    #[verifier::prophetic]
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.index@ <= self.seq().len()
        &&& self.snapshot@.initial_value_inv(self.init@)
        &&& self.wf_inner()
    }

    pub fn new(iter: I, init: Ghost<Option<&'a I>>) -> (s: Self)
        requires
            iter.initial_value_inv(init@),
        ensures
            s.index == 0,
            s.snapshot == iter,
            s.init == init,
            s.iter == iter,
            s.wf(),
    {
        VerusForLoopIterator {
            index: Ghost(0),
            snapshot: Ghost(iter),
            init: init,
            iter,
        }
    }

    pub fn next(&mut self) -> (ret: Option<I::Item>)
        requires 
            old(self).wf(),
        ensures
            self.seq() == old(self).seq(),
            self.index@ == old(self).index@ + if ret is Some { 1int } else { 0 },
            self.snapshot == old(self).snapshot,
            self.init == old(self).init,
            self.iter.obeys_iter_laws() ==> self.wf(),
            self.iter.obeys_iter_laws() && ret is None ==>
                self.snapshot@.completes() && self.index@ == self.seq().len(),
            self.iter.obeys_iter_laws() ==> (ret matches Some(r) ==>
                r == old(self).seq()[old(self).index@]),
            // TODO: Uncomment this line to replace everything below, once general mutable refs are supported
            // call_ensures(I::next, (&mut old(self).iter,), ret),
            self.iter.obeys_iter_laws() == old(self).iter.obeys_iter_laws(),
            self.iter.obeys_iter_laws() ==> self.iter.completes() == old(self).iter.completes(),
            self.iter.obeys_iter_laws() ==> (old(self).iter.decrease() is Some <==> self.iter.decrease() is Some),
            self.iter.obeys_iter_laws() ==> 
            ({
                if old(self).iter.seq().len() > 0 {
                    &&& self.iter.seq() == old(self).iter.seq().drop_first()
                    &&& ret == Some(old(self).iter.seq()[0])
                } else {
                    self.iter.seq() === old(self).iter.seq() && ret === None && self.iter.completes()
                }
            }),
            self.iter.obeys_iter_laws() && old(self).iter.seq().len() > 0 && self.iter.decrease() is Some ==> 
                does_decrease(old(self).iter.decrease(), self.iter.decrease()),
    {
        assert(self.iter.seq().len() == self.seq().len() - self.index@);
        let ret = self.iter.next();
        proof {
            if ret.is_some() {
                self.index@ = self.index@ + 1;
            }
        }
        ret
    }
}

}

// examples
mod examples {

use vstd::prelude::*;
use super::decreases_fix::*;
use super::iterator_traits::*;
broadcast use group_decrease_axioms;


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
        old(iter).decrease() is Some,
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

} // mod examples

} // verus!
