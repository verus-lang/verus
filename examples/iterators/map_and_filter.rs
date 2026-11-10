#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::std_specs::iter::{IteratorSpec, DoubleEndedIteratorSpec, ExactSizeIteratorSpec};
use vstd::proph::ProphecyGhost;

verus! {

/**************************************************************
 *   Define a sequence of prophecies
 **************************************************************/
pub trait Predicate<T> {
    #[verifier::prophetic]
    spec fn pred(&self, i: int, t: T) -> bool;

    #[verifier::prophetic]
    spec fn len(&self) -> nat;
}

#[verifier::accept_recursive_types(T)]
pub tracked struct ProphSeq<T, Pred> {
    // Prophesy each coordinate for every possible original length. This lets
    // rear resolutions use a nonprophetic distance from the back.
    tracked var: ProphecyGhost<spec_fn(nat, int) -> T>,
    // The values of indices that have already been resolved.
    ghost resolved: Map<int, T>,
    ghost resolved_back: Map<int, T>,
    // The predicate this sequence is constrained by.
    ghost p: Pred,
}

impl<T, Pred> ProphSeq<T, Pred>
    where Pred: Predicate<T>
{
    pub closed spec fn pred(&self) -> Pred {
        self.p
    }

    #[verifier::prophetic]
    pub closed spec fn proph_elem(&self, i: int) -> Option<T> {
        let v = if self.resolved.dom().contains(i) {
            self.resolved[i]
        } else if self.resolved_back.dom().contains(self.p.len() - 1 - i) {
            self.resolved_back[self.p.len() - 1 - i]
        } else {
            self.var.value()(self.p.len(), i)
        };
        if self.p.pred(i, v) {
            Some(v)
        } else {
            None
        }
    }

    #[verifier::prophetic]
    pub closed spec fn has_resolved(&self, i: int) -> bool {
        self.resolved.dom().contains(i)
            || self.resolved_back.dom().contains(self.p.len() - 1 - i)
    }

    pub proof fn new(pred: Pred) -> (tracked s: Self)
        ensures
            s.pred() == pred,
            forall |i| !s.has_resolved(i),
    {
        let tracked var = ProphecyGhost::new();
        ProphSeq { var, resolved: Map::empty(), resolved_back: Map::empty(), p: pred }
    }

    pub proof fn proph_elem_meets_pred(tracked &self)
        ensures forall |i: int| (match #[trigger] self.proph_elem(i) {
            Some(p) => self.pred().pred(i, p),
            None => true,
        }),
    {
    }

    pub proof fn resolve(tracked &mut self, i: int, t: T)
        requires
            !old(self).has_resolved(i),
            old(self).pred().pred(i, t),
        ensures
            final(self).pred() == old(self).pred(),
            forall |j| final(self).proph_elem(j) == old(self).proph_elem(j),
            forall |j| i != j ==> final(self).has_resolved(j) == old(self).has_resolved(j),
            final(self).has_resolved(i),
            final(self).proph_elem(i) == Some(t),
    {
        // Peel off coordinate `i`: replace the live prophecy with a fresh one
        // holding the remaining (still prophetic) coordinates, and resolve the
        // old prophecy as a function of the fresh one that pins index `i` to `t`.
        let tracked mut var = ProphecyGhost::new();
        vstd::modes::tracked_swap(&mut var, &mut self.var);
        var.resolve_dependent(
            &self.var,
            |g: spec_fn(nat, int) -> T|
                (|n: nat, j: int| if j == i { t } else { g(n, j) }),
        );
        self.resolved = self.resolved.insert(i, t);

        assert forall |j| #[trigger] final(self).proph_elem(j) == old(self).proph_elem(j) by {
            if j != i && !old(self).resolved.dom().contains(j) {
                // Unresolved (other) coordinate: old and fresh prophecy agree.
                assert(old(self).var.value()(old(self).p.len(), j)
                    == final(self).var.value()(final(self).p.len(), j));
            }
        }
    }

    pub proof fn resolve_back(tracked &mut self, back: int, t: T)
        requires
            !old(self).has_resolved(old(self).pred().len() - 1 - back),
            old(self).pred().pred(old(self).pred().len() - 1 - back, t),
        ensures
            final(self).pred() == old(self).pred(),
            forall |j| final(self).proph_elem(j) == old(self).proph_elem(j),
            forall |j| j != old(self).pred().len() - 1 - back ==>
                final(self).has_resolved(j) == old(self).has_resolved(j),
            final(self).has_resolved(old(self).pred().len() - 1 - back),
            final(self).proph_elem(old(self).pred().len() - 1 - back) == Some(t),
    {
        let tracked mut var = ProphecyGhost::new();
        vstd::modes::tracked_swap(&mut var, &mut self.var);
        var.resolve_dependent(
            &self.var,
            |g: spec_fn(nat, int) -> T|
                (|n: nat, j: int| if j == n - 1 - back { t } else { g(n, j) }),
        );
        self.resolved_back = self.resolved_back.insert(back, t);
    }
}

/**************************************************************
 *            Implement Iterator::Map                         *
 **************************************************************/

pub ghost struct MapIteratorPred<Iter, F> {
    iter: Iter,
    f: F,
}

impl<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> Predicate<Item> for MapIteratorPred<
    Iter,
    F,
> {
    #[verifier::prophetic]
    closed spec fn pred(&self, i: int, t: Item) -> bool {
        self.iter.produces()[i] && call_ensures(self.f, (self.iter.remaining()[i],), t)
    }

    #[verifier::prophetic]
    closed spec fn len(&self) -> nat {
        self.iter.remaining().len()
    }
}

#[verifier::reject_recursive_types(Item)]
struct MapIteratorState<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> {
    f: F,
    iter: Iter,
    prophs: Tracked<ProphSeq<Item, MapIteratorPred<Iter, F>>>,
    idx: Ghost<int>,
    back: Ghost<int>,
}

impl<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> MapIteratorState<Item, Iter, F> {
    #[verifier::prophetic]
    spec fn wf(self) -> bool {
        &&& self.iter.obeys_prophetic_iter_laws()
            == self.prophs@.pred().iter.obeys_prophetic_iter_laws()
        &&& self.prophs@.pred().f == self.f
        &&& if self.iter.obeys_prophetic_iter_laws() {
            &&& 0 <= self.idx@
            &&& 0 <= self.back@
            &&& self.idx@ + self.iter.remaining().len() + self.back@
                == self.prophs@.pred().iter.remaining().len()
            &&& self.iter.remaining() == self.prophs@.pred().iter.remaining()[self.idx@..self.idx@
                + self.iter.remaining().len()]
            &&& forall|i: int|
                0 <= i < self.iter.remaining().len() ==> #[trigger] self.iter.produces()[i]
                    == self.prophs@.pred().iter.produces()[self.idx@ + i]
            &&& forall|i|
                #![auto]
                0 <= i < self.iter.remaining().len() && self.iter.produces()[i] ==> call_requires(
                    self.f,
                    (self.iter.remaining()[i],),
                )
            &&& forall|i: int|
                self.idx@ <= i < self.idx@ + self.iter.remaining().len()
                    ==> !self.prophs@.has_resolved(i)
        } else {
            forall|x: Iter::Item| #![auto] call_requires(self.f, (x,))
        }
    }

    #[verifier::prophetic]
    spec fn options(self) -> Seq<Option<Item>> {
        Seq::new(self.iter.remaining().len(), |i| self.prophs@.proph_elem(self.idx@ + i))
    }

    #[verifier::prophetic]
    spec fn remaining(self) -> Seq<Item> {
        // Unproduced positions still have a slot; their value is unconstrained.
        Seq::new(
            self.options().len(),
            |i|
                match self.options()[i] {
                    Some(value) => value,
                    None => arbitrary(),
                },
        )
    }

    #[verifier::prophetic]
    spec fn produces(self) -> Seq<bool> {
        Seq::new(self.options().len(), |i| self.iter.produces()[i] && self.options()[i].is_some())
    }

    fn next(mut self) -> (out: (Self, Option<Item>))
        requires
            self.wf(),
        ensures
            out.0.wf(),
            out.0.iter.obeys_prophetic_iter_laws() == self.iter.obeys_prophetic_iter_laws(),
            self.iter.obeys_prophetic_iter_laws() ==> out.0.iter.decrease() is Some
                == self.iter.decrease() is Some,
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() > 0 ==> {
                &&& out.0.remaining() == self.remaining().drop_first()
                &&& out.0.produces() == self.produces().drop_first()
                &&& out.1 == Some(self.remaining()[0])
                &&& self.produces()[0]
                &&& out.0.iter.decrease() is Some
                    ==> decreases_to!(self.iter.decrease()->0 => out.0.iter.decrease()->0)
            },
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() == 0 ==> {
                &&& out.0.remaining() == self.remaining()
                &&& out.0.produces() == self.produces()
                &&& out.1 == None
            },
    {
        let ghost initial = self;
        match self.iter.next() {
            None => {
                assert(self.wf());
                (self, None)
            },
            Some(elem) => {
                let output = (self.f)(elem);
                proof {
                    if initial.iter.obeys_prophetic_iter_laws() {
                        self.prophs.borrow_mut().resolve(self.idx@, output);
                        self.idx@ = self.idx@ + 1;
                        assert(self.options() =~= initial.options().drop_first());
                        assert(self.remaining() =~= initial.remaining().drop_first());
                        assert(self.produces() =~= initial.produces().drop_first());
                        assert(self.iter.remaining()
                            =~= self.prophs@.pred().iter.remaining()[self.idx@..self.idx@
                            + self.iter.remaining().len()]);
                        assert(self.wf());
                    }
                }
                (self, Some(output))
            },
        }
    }
}

impl<Item, Iter: DoubleEndedIterator, F: FnMut(Iter::Item) -> Item>
    MapIteratorState<Item, Iter, F>
{
    fn next_back(mut self) -> (out: (Self, Option<Item>))
        requires
            self.wf(),
        ensures
            out.0.wf(),
            out.0.iter.obeys_prophetic_iter_laws() == self.iter.obeys_prophetic_iter_laws(),
            self.iter.obeys_prophetic_iter_laws() ==> out.0.iter.decrease() is Some
                == self.iter.decrease() is Some,
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() > 0 ==> {
                &&& out.0.remaining() == self.remaining().drop_last()
                &&& out.0.produces() == self.produces().drop_last()
                &&& out.1 == Some(self.remaining().last())
                &&& self.produces().last()
                &&& out.0.iter.decrease() is Some
                    ==> self.iter.decrease()->0 > out.0.iter.decrease()->0
            },
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() == 0 ==> {
                &&& out.0.remaining() == self.remaining()
                &&& out.0.produces() == self.produces()
                &&& out.1 == None
            },
    {
        let ghost initial = self;
        match self.iter.next_back() {
            None => (self, None),
            Some(elem) => {
                let output = (self.f)(elem);
                proof {
                    if initial.iter.obeys_prophetic_iter_laws() {
                        self.prophs.borrow_mut().resolve_back(self.back@, output);
                        self.back@ = self.back@ + 1;
                        assert(self.options() =~= initial.options().drop_last());
                        assert(self.remaining() =~= initial.remaining().drop_last());
                        assert(self.produces() =~= initial.produces().drop_last());
                        assert(self.iter.remaining()
                            =~= self.prophs@.pred().iter.remaining()[self.idx@..self.idx@
                            + self.iter.remaining().len()]);
                        assert(self.wf());
                    }
                }
                (self, Some(output))
            },
        }
    }
}

// Take the state out before calling the iterator or closure: either may unwind.
// The empty wrapper satisfies its invariant while the local state is being changed.
#[verifier::reject_recursive_types(Item)]
pub struct MapIterator<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> {
    state: Option<MapIteratorState<Item, Iter, F>>,
}

impl<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> MapIterator<Item, Iter, F> {
    #[verifier::type_invariant]
    #[verifier::prophetic]
    spec fn wf(self) -> bool {
        self.state matches Some(s) ==> s.wf()
    }

    pub closed spec fn inner(self) -> Iter {
        self.state.unwrap().iter
    }

    pub closed spec fn func(self) -> F {
        self.state.unwrap().f
    }

    pub closed spec fn the_prophs(self) -> ProphSeq<Item, MapIteratorPred<Iter, F>> {
        self.state.unwrap().prophs@
    }

    pub closed spec fn count(self) -> nat {
        self.state.unwrap().idx@ as nat
    }

    pub fn new(iter: Iter, f: F) -> (s: Self)
        requires
            iter.obeys_prophetic_iter_laws() ==> forall|i|
                #![auto]
                0 <= i < iter.remaining().len() && iter.produces()[i] ==> call_requires(
                    f,
                    (iter.remaining()[i],),
                ),
            !iter.obeys_prophetic_iter_laws() ==> forall|x: Iter::Item|
                #![auto]
                call_requires(f, (x,)),
        ensures
            s.obeys_prophetic_iter_laws() == iter.obeys_prophetic_iter_laws(),
            iter.obeys_prophetic_iter_laws() ==> s.remaining().len() == iter.remaining().len(),
            s.produces().len() == s.remaining().len(),
            iter.obeys_prophetic_iter_laws() ==> forall|i|
                #![auto]
                0 <= i < s.remaining().len() && s.produces()[i] ==> iter.produces()[i]
                    && call_ensures(f, (iter.remaining()[i],), s.remaining()[i]),
            s.count() == 0,
            s.inner() == iter,
            s.func() == f,
            s.decrease() is Some == iter.decrease() is Some,
    {
        let state = MapIteratorState {
            f,
            iter,
            prophs: Tracked(ProphSeq::new(MapIteratorPred { iter, f })),
            idx: Ghost(0),
            back: Ghost(0),
        };
        proof {
            assert(iter.remaining()[0..iter.remaining().len()] =~= iter.remaining());
            state.prophs.borrow().proph_elem_meets_pred();
        }
        MapIterator { state: Some(state) }
    }
}

impl<Item, Iter: Iterator, F: FnMut(Iter::Item) -> Item> Iterator for MapIterator<Item, Iter, F> {
    type Item = Item;

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.state {
            None => (0, Some(0)),
            Some(state) => state.iter.size_hint(),
        }
    }

    fn next(&mut self) -> (ret: Option<Item>) {
        proof {
            use_type_invariant(&*self);
        }
        match self.state.take() {
            None => None,
            Some(state) => {
                let (state, ret) = state.next();
                self.state = Some(state);
                ret
            },
        }
    }
}

impl<
    Item,
    Iter: Iterator,
    F: FnMut(Iter::Item) -> Item,
> vstd::std_specs::iter::IteratorSpecImpl for MapIterator<Item, Iter, F> {
    closed spec fn obeys_prophetic_iter_laws(&self) -> bool {
        match self.state {
            Some(s) => s.iter.obeys_prophetic_iter_laws(),
            None => true,
        }
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Item> {
        match self.state {
            Some(s) => s.remaining(),
            None => seq![],
        }
    }

    #[verifier::prophetic]
    closed spec fn produces(&self) -> Seq<bool> {
        match self.state {
            Some(s) => s.produces(),
            None => seq![],
        }
    }

    closed spec fn decrease(&self) -> Option<nat> {
        match self.state {
            Some(s) => s.iter.decrease(),
            None => None,
        }
    }

    open spec fn peek(&self, index: int) -> Option<Item> {
        match self.inner().peek(index) {
            Some(v) => Some(choose|x| self.func().ensures((v,), x)),
            None => None,
        }
    }
}

impl<Item, Iter: DoubleEndedIterator, F: FnMut(Iter::Item) -> Item> DoubleEndedIterator
    for MapIterator<Item, Iter, F>
{
    fn next_back(&mut self) -> Option<Item> {
        proof { use_type_invariant(&*self); }
        match self.state.take() {
            None => None,
            Some(state) => {
                let (state, ret) = state.next_back();
                self.state = Some(state);
                ret
            },
        }
    }
}

impl<Item, Iter: DoubleEndedIterator, F: FnMut(Iter::Item) -> Item>
    vstd::std_specs::iter::DoubleEndedIteratorSpecImpl for MapIterator<Item, Iter, F>
{
    open spec fn peek_back(&self, index: int) -> Option<Item> {
        match self.inner().peek_back(index) {
            Some(v) => Some(choose|x| self.func().ensures((v,), x)),
            None => None,
        }
    }
}

impl<Item, Iter: ExactSizeIterator, F: FnMut(Iter::Item) -> Item> ExactSizeIterator
    for MapIterator<Item, Iter, F>
{
    fn len(&self) -> usize {
        match &self.state {
            None => 0,
            Some(state) => state.iter.len(),
        }
    }
}

impl<Item, Iter: ExactSizeIterator, F: FnMut(Iter::Item) -> Item>
    vstd::std_specs::iter::ExactSizeIteratorSpecImpl for MapIterator<Item, Iter, F>
{
    closed spec fn exact_len(&self) -> usize {
        match self.state {
            None => 0,
            Some(state) => state.iter.exact_len(),
        }
    }
}

/**************************************************************
 *            Implement Iterator::Filter                      *
 **************************************************************/

// Filtering sequences of equal length with the same predicate selects the same
// source indices. The rank of an index is the length of its filtered prefix.
proof fn lemma_filter_index_at_rank<T, U>(s: Seq<T>, t: Seq<U>, p: spec_fn(int) -> bool, j: int)
    requires
        s.len() == t.len(),
        0 <= j < s.len(),
        p(j),
    ensures
        ({
            let k = s[..j].filter_index(p).len() as int;
            &&& k < s.filter_index(p).len()
            &&& s.filter_index(p)[k] == s[j]
            &&& t.filter_index(p)[k] == t[j]
        }),
    decreases s.len(),
{
    reveal(Seq::filter_index);
    let last = s.len() - 1;
    lemma_filter_index_length(s.drop_last(), t.drop_last(), p);
    if j < last {
        lemma_filter_index_at_rank(s.drop_last(), t.drop_last(), p, j);
        assert(s[..j] =~= s.drop_last()[..j]);
    } else {
        assert(s[..j] =~= s.drop_last());
    }
}

proof fn lemma_filter_index_length<T, U>(s: Seq<T>, t: Seq<U>, p: spec_fn(int) -> bool)
    requires
        s.len() == t.len(),
    ensures
        s.filter_index(p).len() == t.filter_index(p).len(),
    decreases s.len(),
{
    reveal(Seq::filter_index);
    if s.len() > 0 {
        lemma_filter_index_length(s.drop_last(), t.drop_last(), p);
    }
}

proof fn lemma_filter_index_witness_pair<T, U>(
    s: Seq<T>,
    t: Seq<U>,
    p: spec_fn(int) -> bool,
    k: int,
)
    requires
        s.len() == t.len(),
        0 <= k < s.filter_index(p).len(),
    ensures
        exists|j: int|
            0 <= j < s.len() && p(j) && k == s[..j].filter_index(p).len() && s.filter_index(p)[k]
                == s[j] && t.filter_index(p)[k] == t[j],
    decreases s.len(),
{
    reveal(Seq::filter_index);
    let last = s.len() - 1;
    lemma_filter_index_length(s.drop_last(), t.drop_last(), p);
    if p(last) && k == s.drop_last().filter_index(p).len() {
        assert(s[..last] =~= s.drop_last());
        assert(s.filter_index(p)[k] == s[last]);
        assert(t.filter_index(p)[k] == t[last]);
    } else {
        assert(0 <= k < s.drop_last().filter_index(p).len());
        lemma_filter_index_witness_pair(s.drop_last(), t.drop_last(), p, k);
        let j = choose|j: int|
            0 <= j < s.drop_last().len() && p(j) && k == s.drop_last()[..j].filter_index(p).len()
                && s.drop_last().filter_index(p)[k] == s.drop_last()[j]
                && t.drop_last().filter_index(p)[k] == t.drop_last()[j];
        assert(s[..j] =~= s.drop_last()[..j]);
        assert(s.filter_index(p)[k] == s[j]);
        assert(t.filter_index(p)[k] == t[j]);
    }
}

pub ghost struct FilterIteratorPred<Iter, F> {
    iter: Iter,
    f: F,
}

impl<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> Predicate<bool> for FilterIteratorPred<
    Iter,
    F,
> {
    #[verifier::prophetic]
    closed spec fn pred(&self, i: int, b: bool) -> bool {
        self.iter.produces()[i] && call_ensures(self.f, (&self.iter.remaining()[i],), b)
    }

    #[verifier::prophetic]
    closed spec fn len(&self) -> nat {
        self.iter.remaining().len()
    }
}

struct FilterIteratorState<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> {
    f: F,
    iter: Iter,
    prophs: Tracked<ProphSeq<bool, FilterIteratorPred<Iter, F>>>,
    idx: Ghost<int>,
    back: Ghost<int>,
}

impl<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> FilterIteratorState<Iter, F> {
    #[verifier::prophetic]
    spec fn wf(self) -> bool {
        &&& self.iter.obeys_prophetic_iter_laws()
            == self.prophs@.pred().iter.obeys_prophetic_iter_laws()
        &&& self.prophs@.pred().f == self.f
        &&& if self.iter.obeys_prophetic_iter_laws() {
            &&& 0 <= self.idx@
            &&& 0 <= self.back@
            &&& self.idx@ + self.iter.remaining().len() + self.back@
                == self.prophs@.pred().iter.remaining().len()
            &&& self.iter.remaining() == self.prophs@.pred().iter.remaining()[self.idx@..self.idx@
                + self.iter.remaining().len()]
            &&& forall|i: int|
                0 <= i < self.iter.remaining().len() ==> #[trigger] self.iter.produces()[i]
                    == self.prophs@.pred().iter.produces()[self.idx@ + i]
            &&& forall|i|
                #![auto]
                0 <= i < self.iter.remaining().len() && self.iter.produces()[i] ==> call_requires(
                    self.f,
                    (&self.iter.remaining()[i],),
                )
            &&& forall|i: int|
                self.idx@ <= i < self.idx@ + self.iter.remaining().len()
                    ==> !self.prophs@.has_resolved(
                    i,
                )
                // Lawful steps preserve and decrease the progress metric.
            &&& self.iter.decrease() is Some
        } else {
            forall|x: &Iter::Item| #![auto] call_requires(self.f, (x,))
        }
    }

    #[verifier::prophetic]
    spec fn options(self) -> Seq<Option<bool>> {
        Seq::new(self.iter.remaining().len(), |i| self.prophs@.proph_elem(self.idx@ + i))
    }

    #[verifier::prophetic]
    spec fn keep(self) -> Seq<bool> {
        // A stuck position is retained rather than discarded.
        Seq::new(self.options().len(), |i| self.options()[i] != Some(false))
    }

    #[verifier::prophetic]
    spec fn keep_pred(self) -> spec_fn(int) -> bool {
        |i: int| self.keep()[i]
    }

    #[verifier::prophetic]
    spec fn remaining(self) -> Seq<Iter::Item> {
        self.iter.remaining().filter_index(self.keep_pred())
    }

    #[verifier::prophetic]
    spec fn inner_produces(self) -> Seq<bool> {
        Seq::new(
            self.options().len(),
            |i| self.iter.produces()[i] && self.options()[i] == Some(true),
        )
    }

    #[verifier::prophetic]
    spec fn produces(self) -> Seq<bool> {
        self.inner_produces().filter_index(self.keep_pred())
    }

    // Without the iterator laws there is no progress guarantee for the loop.
    #[verifier::exec_allows_no_decreases_clause]
    fn next(self) -> (out: (Self, Option<Iter::Item>))
        requires
            self.wf(),
        ensures
            out.0.wf(),
            self.produces().len() == self.remaining().len(),
            out.0.iter.obeys_prophetic_iter_laws() == self.iter.obeys_prophetic_iter_laws(),
            self.iter.obeys_prophetic_iter_laws() ==> out.0.iter.decrease() is Some,
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() > 0 ==> {
                &&& out.0.remaining() == self.remaining().drop_first()
                &&& out.0.produces() == self.produces().drop_first()
                &&& out.1 == Some(self.remaining()[0])
                &&& self.produces()[0]
                &&& decreases_to!(self.iter.decrease()->0 => out.0.iter.decrease()->0)
            },
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() == 0 ==> {
                &&& out.0.remaining() == self.remaining()
                &&& out.0.produces() == self.produces()
                &&& out.1 == None
            },
    {
        let mut state = self;
        let ghost initial = self;
        proof {
            lemma_filter_index_length(
                state.iter.remaining(),
                state.inner_produces(),
                state.keep_pred(),
            );
        }
        loop
            invariant
                state.wf(),
                initial.wf(),
                initial == self,
                state.iter.obeys_prophetic_iter_laws() == initial.iter.obeys_prophetic_iter_laws(),
                initial.iter.obeys_prophetic_iter_laws() ==> state.iter.decrease()->0
                    <= initial.iter.decrease()->0,
                state.idx@ >= initial.idx@,
                initial.iter.obeys_prophetic_iter_laws() ==> state.remaining()
                    == initial.remaining(),
                initial.iter.obeys_prophetic_iter_laws() ==> state.produces() == initial.produces(),
                initial.produces().len() == initial.remaining().len(),
        {
            let ghost head = state;
            match state.iter.next() {
                None => {
                    proof {
                        reveal(Seq::filter_index);
                    }
                    return (state, None);
                },
                Some(item) => {
                    let keep = (state.f)(&item);
                    proof {
                        if initial.iter.obeys_prophetic_iter_laws() {
                            state.prophs.borrow_mut().resolve(state.idx@, keep);
                            state.idx@ = state.idx@ + 1;
                            assert(state.options() =~= head.options().drop_first());
                            assert(state.keep() =~= head.keep().drop_first());
                            assert(state.inner_produces() =~= head.inner_produces().drop_first());
                            assert(state.iter.remaining()
                                =~= state.prophs@.pred().iter.remaining()[state.idx@..state.idx@
                                + state.iter.remaining().len()]);
                            lemma_filter_step(head, state, keep);
                        }
                    }
                    if keep {
                        assert(initial.iter.obeys_prophetic_iter_laws() ==> state.remaining()
                            =~= initial.remaining().drop_first());
                        assert(initial.iter.obeys_prophetic_iter_laws() ==> state.produces()
                            =~= initial.produces().drop_first());
                        return (state, Some(item));
                    }
                },
            }
        }
    }
}

impl<Iter: DoubleEndedIterator, F: FnMut(&Iter::Item) -> bool> FilterIteratorState<Iter, F> {
    #[verifier::exec_allows_no_decreases_clause]
    fn next_back(self) -> (out: (Self, Option<Iter::Item>))
        requires
            self.wf(),
        ensures
            out.0.wf(),
            self.produces().len() == self.remaining().len(),
            out.0.iter.obeys_prophetic_iter_laws() == self.iter.obeys_prophetic_iter_laws(),
            self.iter.obeys_prophetic_iter_laws() ==> out.0.iter.decrease() is Some,
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() > 0 ==> {
                &&& out.0.remaining() == self.remaining().drop_last()
                &&& out.0.produces() == self.produces().drop_last()
                &&& out.1 == Some(self.remaining().last())
                &&& self.produces().last()
                &&& self.iter.decrease()->0 > out.0.iter.decrease()->0
            },
            self.iter.obeys_prophetic_iter_laws() && self.remaining().len() == 0 ==> {
                &&& out.0.remaining() == self.remaining()
                &&& out.0.produces() == self.produces()
                &&& out.1 == None
            },
    {
        let mut state = self;
        let ghost initial = self;
        proof {
            lemma_filter_index_length(
                state.iter.remaining(),
                state.inner_produces(),
                state.keep_pred(),
            );
        }
        loop
            invariant
                state.wf(),
                initial.wf(),
                initial == self,
                state.iter.obeys_prophetic_iter_laws() == initial.iter.obeys_prophetic_iter_laws(),
                initial.iter.obeys_prophetic_iter_laws() ==> state.iter.decrease()->0
                    <= initial.iter.decrease()->0,
                initial.iter.obeys_prophetic_iter_laws() ==> state.remaining()
                    == initial.remaining(),
                initial.iter.obeys_prophetic_iter_laws() ==> state.produces() == initial.produces(),
                initial.produces().len() == initial.remaining().len(),
        {
            let ghost head = state;
            match state.iter.next_back() {
                None => {
                    proof { reveal(Seq::filter_index); }
                    return (state, None);
                },
                Some(item) => {
                    let keep = (state.f)(&item);
                    proof {
                        if initial.iter.obeys_prophetic_iter_laws() {
                            state.prophs.borrow_mut().resolve_back(state.back@, keep);
                            state.back@ = state.back@ + 1;
                            assert(state.options() =~= head.options().drop_last());
                            assert(state.keep() =~= head.keep().drop_last());
                            assert(state.inner_produces() =~= head.inner_produces().drop_last());
                            assert(state.iter.remaining()
                                =~= state.prophs@.pred().iter.remaining()[state.idx@..state.idx@
                                + state.iter.remaining().len()]);
                            lemma_filter_back_step(head, state, keep);
                        }
                    }
                    if keep {
                        assert(initial.iter.obeys_prophetic_iter_laws() ==> state.remaining()
                            =~= initial.remaining().drop_last());
                        assert(initial.iter.obeys_prophetic_iter_laws() ==> state.produces()
                            =~= initial.produces().drop_last());
                        return (state, Some(item));
                    }
                },
            }
        }
    }
}

proof fn lemma_filter_back_step<Iter: Iterator, F: FnMut(&Iter::Item) -> bool>(
    head: FilterIteratorState<Iter, F>,
    tail: FilterIteratorState<Iter, F>,
    b: bool,
)
    requires
        head.iter.remaining().len() > 0,
        head.iter.produces().len() == head.iter.remaining().len(),
        head.options().last() == Some(b),
        head.iter.produces().last(),
        tail.iter.remaining() == head.iter.remaining().drop_last(),
        tail.keep() == head.keep().drop_last(),
        tail.inner_produces() == head.inner_produces().drop_last(),
    ensures
        b ==> head.remaining() == tail.remaining() + seq![head.iter.remaining().last()],
        !b ==> head.remaining() == tail.remaining(),
        b ==> head.produces() == tail.produces() + seq![true],
        !b ==> head.produces() == tail.produces(),
{
    reveal(Seq::filter_index);
    head.iter.remaining().drop_last().filter_index_ext(head.keep_pred(), tail.keep_pred());
    head.inner_produces().drop_last().filter_index_ext(head.keep_pred(), tail.keep_pred());
}

proof fn lemma_filter_step<Iter: Iterator, F: FnMut(&Iter::Item) -> bool>(
    head: FilterIteratorState<Iter, F>,
    tail: FilterIteratorState<Iter, F>,
    b: bool,
)
    requires
        head.iter.remaining().len() > 0,
        head.options()[0] == Some(b),
        head.iter.produces()[0],
        tail.iter.remaining() == head.iter.remaining().drop_first(),
        tail.keep() == head.keep().drop_first(),
        tail.inner_produces() == head.inner_produces().drop_first(),
    ensures
        b ==> head.remaining() == seq![head.iter.remaining()[0]] + tail.remaining(),
        !b ==> head.remaining() == tail.remaining(),
        b ==> head.produces() == seq![true] + tail.produces(),
        !b ==> head.produces() == tail.produces(),
{
    let p = |i: int| head.keep()[i];
    let q = |i: int| tail.keep()[i];
    head.iter.remaining().lemma_filter_index_head(p);
    head.inner_produces().lemma_filter_index_head(p);
    head.iter.remaining().drop_first().filter_index_ext(|i: int| p(i + 1), q);
    head.inner_produces().drop_first().filter_index_ext(|i: int| p(i + 1), q);
}

proof fn lemma_filter_description<Iter: Iterator, F: FnMut(&Iter::Item) -> bool>(
    state: FilterIteratorState<Iter, F>,
)
    requires
        state.wf(),
        state.iter.obeys_prophetic_iter_laws(),
    ensures
        state.produces().len() == state.remaining().len(),
        state.remaining().len() <= state.iter.remaining().len(),
        forall|j|
            0 <= j < state.keep().len() && !(#[trigger] state.keep()[j])
                ==> state.iter.produces()[j] && call_ensures(
                state.f,
                (&state.iter.remaining()[j],),
                false,
            ),
        forall|j|
            0 <= j < state.keep().len() && #[trigger] state.keep()[j] ==> {
                let k = state.iter.remaining()[..j].filter_index(state.keep_pred()).len() as int;
                state.produces()[k] ==> state.iter.produces()[j] && call_ensures(
                    state.f,
                    (&state.iter.remaining()[j],),
                    true,
                )
            },
{
    let p = state.keep_pred();
    lemma_filter_index_length(state.iter.remaining(), state.inner_produces(), p);
    broadcast use Seq::lemma_filter_index;

    assert forall|j| 0 <= j < state.keep().len() && #[trigger] state.keep()[j] implies {
        let k = state.iter.remaining()[..j].filter_index(state.keep_pred()).len() as int;
        state.produces()[k] ==> state.iter.produces()[j] && call_ensures(
            state.f,
            (&state.iter.remaining()[j],),
            true,
        )
    } by {
        let k = state.iter.remaining()[..j].filter_index(p).len() as int;
        lemma_filter_index_at_rank(state.iter.remaining(), state.inner_produces(), p, j);
        assert(state.produces()[k] == state.inner_produces()[j]);
        if state.produces()[k] {
            assert(state.options()[j] == Some(true));
            assert(state.prophs@.pred().pred(state.idx@ + j, true));
        }
    }
}

proof fn lemma_filter_source<Iter: Iterator, F: FnMut(&Iter::Item) -> bool>(
    state: FilterIteratorState<Iter, F>,
    k: int,
)
    requires
        state.wf(),
        state.iter.obeys_prophetic_iter_laws(),
        0 <= k < state.remaining().len(),
    ensures
        exists|j: int|
            #![auto]
            0 <= j < state.iter.remaining().len() && state.remaining()[k]
                == state.iter.remaining()[j] && state.keep()[j] && k
                == state.iter.remaining()[..j].filter_index(state.keep_pred()).len() && (
            state.produces()[k] ==> state.iter.produces()[j] && call_ensures(
                state.f,
                (&state.iter.remaining()[j],),
                true,
            )),
{
    let p = state.keep_pred();
    lemma_filter_index_witness_pair(state.iter.remaining(), state.inner_produces(), p, k);
    let j = choose|j: int|
        #![auto]
        0 <= j < state.iter.remaining().len() && p(j) && k
            == state.iter.remaining()[..j].filter_index(p).len() && state.remaining()[k]
            == state.iter.remaining()[j] && state.produces()[k] == state.inner_produces()[j];
    if state.produces()[k] {
        assert(state.options()[j] == Some(true));
        assert(state.prophs@.pred().pred(state.idx@ + j, true));
    }
    assert(exists|w: int|
        #![auto]
        0 <= w < state.iter.remaining().len() && state.remaining()[k] == state.iter.remaining()[w]
            && state.keep()[w] && k == state.iter.remaining()[..w].filter_index(
            state.keep_pred(),
        ).len() && (state.produces()[k] ==> state.iter.produces()[w] && call_ensures(
            state.f,
            (&state.iter.remaining()[w],),
            true,
        )));
}

pub open spec fn filter_has_source<T, F: FnMut(&T) -> bool>(
    input: Seq<T>,
    input_produces: Seq<bool>,
    remaining: Seq<T>,
    produces: Seq<bool>,
    keep: Seq<bool>,
    f: F,
    k: int,
) -> bool {
    exists|j: int|
        #![auto]
        0 <= j < input.len() && remaining[k] == input[j] && keep[j] && k == input[..j].filter_index(
            |idx: int| keep[idx],
        ).len() && (produces[k] ==> input_produces[j] && call_ensures(f, (&input[j],), true))
}

pub struct FilterIterator<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> {
    state: Option<FilterIteratorState<Iter, F>>,
}

impl<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> FilterIterator<Iter, F> {
    #[verifier::type_invariant]
    #[verifier::prophetic]
    spec fn wf(self) -> bool {
        self.state matches Some(s) ==> s.wf()
    }

    #[verifier::prophetic]
    spec fn spec_remaining(self) -> Seq<Iter::Item> {
        match self.state {
            Some(s) => s.remaining(),
            None => seq![],
        }
    }

    #[verifier::prophetic]
    spec fn spec_produces(self) -> Seq<bool> {
        match self.state {
            Some(s) => s.produces(),
            None => seq![],
        }
    }

    pub closed spec fn inner(self) -> Iter {
        self.state.unwrap().iter
    }

    pub closed spec fn func(self) -> F {
        self.state.unwrap().f
    }

    pub closed spec fn the_prophs(self) -> ProphSeq<bool, FilterIteratorPred<Iter, F>> {
        self.state.unwrap().prophs@
    }

    pub closed spec fn count(self) -> nat {
        self.state.unwrap().idx@ as nat
    }

    #[verifier::prophetic]
    pub closed spec fn keep(self) -> Seq<bool> {
        match self.state {
            Some(s) => s.keep(),
            None => seq![],
        }
    }

    #[verifier::prophetic]
    pub closed spec fn keep_pred(self) -> spec_fn(int) -> bool {
        match self.state {
            Some(s) => s.keep_pred(),
            None => |i: int| false,
        }
    }

    pub fn new(iter: Iter, f: F) -> (s: Self)
        requires
            iter.decrease() is Some,
            iter.obeys_prophetic_iter_laws() ==> forall|i|
                #![auto]
                0 <= i < iter.remaining().len() && iter.produces()[i] ==> call_requires(
                    f,
                    (&iter.remaining()[i],),
                ),
            !iter.obeys_prophetic_iter_laws() ==> forall|x: &Iter::Item|
                #![auto]
                call_requires(f, (x,)),
        ensures
            s.obeys_prophetic_iter_laws() == iter.obeys_prophetic_iter_laws(),
            iter.obeys_prophetic_iter_laws() ==> s.keep().len() == iter.remaining().len(),
            s.keep_pred() == (|i: int| s.keep()[i]),
            iter.obeys_prophetic_iter_laws() ==> forall|j|
                0 <= j < s.keep().len() && !(#[trigger] s.keep()[j]) ==> iter.produces()[j]
                    && call_ensures(f, (&iter.remaining()[j],), false),
            iter.obeys_prophetic_iter_laws() ==> forall|j|
                0 <= j < s.keep().len() && #[trigger] s.keep()[j] ==> {
                    let k = iter.remaining()[..j].filter_index(s.keep_pred()).len() as int;
                    s.produces()[k] ==> iter.produces()[j] && call_ensures(
                        f,
                        (&iter.remaining()[j],),
                        true,
                    )
                },
            iter.obeys_prophetic_iter_laws() ==> s.remaining() == iter.remaining().filter_index(
                s.keep_pred(),
            ),
            iter.obeys_prophetic_iter_laws() ==> s.produces().len() == s.remaining().len(),
            iter.obeys_prophetic_iter_laws() ==> s.remaining().len() <= iter.remaining().len(),
            iter.obeys_prophetic_iter_laws() ==> forall|k|
                0 <= k < s.remaining().len() ==> #[trigger] filter_has_source(
                    iter.remaining(),
                    iter.produces(),
                    s.remaining(),
                    s.produces(),
                    s.keep(),
                    f,
                    k,
                ),
            s.count() == 0,
            s.inner() == iter,
            s.func() == f,
            s.decrease() is Some == iter.decrease() is Some,
    {
        let state = FilterIteratorState {
            f,
            iter,
            prophs: Tracked(ProphSeq::new(FilterIteratorPred { iter, f })),
            idx: Ghost(0),
            back: Ghost(0),
        };
        proof {
            assert(iter.remaining()[0..iter.remaining().len()] =~= iter.remaining());
            state.prophs.borrow().proph_elem_meets_pred();
            if iter.obeys_prophetic_iter_laws() {
                lemma_filter_description(state);
            }
        }
        let s = FilterIterator { state: Some(state) };
        proof {
            assert(state.keep_pred() =~= (|i: int| s.keep()[i]));
            let keep = s.keep();
            assert(state.keep_pred() =~= (|i: int| keep[i]));
            assert forall|k|
                iter.obeys_prophetic_iter_laws() && 0 <= k
                    < s.remaining().len() implies #[trigger] filter_has_source(
                iter.remaining(),
                iter.produces(),
                s.remaining(),
                s.produces(),
                s.keep(),
                f,
                k,
            ) by {
                lemma_filter_source(state, k);
            }
        }
        s
    }
}

impl<Iter: Iterator, F: FnMut(&Iter::Item) -> bool> Iterator for FilterIterator<Iter, F> {
    type Item = Iter::Item;

    fn next(&mut self) -> (ret: Option<Self::Item>) {
        proof {
            use_type_invariant(&*self);
        }
        match self.state.take() {
            None => None,
            Some(state) => {
                let (state, ret) = state.next();
                self.state = Some(state);
                ret
            },
        }
    }
}

impl<
    Iter: Iterator,
    F: FnMut(&Iter::Item) -> bool,
> vstd::std_specs::iter::IteratorSpecImpl for FilterIterator<Iter, F> {
    closed spec fn obeys_prophetic_iter_laws(&self) -> bool {
        match self.state {
            Some(s) => s.iter.obeys_prophetic_iter_laws(),
            None => true,
        }
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        self.spec_remaining()
    }

    #[verifier::prophetic]
    closed spec fn produces(&self) -> Seq<bool> {
        self.spec_produces()
    }

    closed spec fn decrease(&self) -> Option<nat> {
        match self.state {
            Some(s) => s.iter.decrease(),
            None => None,
        }
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

impl<Iter: DoubleEndedIterator, F: FnMut(&Iter::Item) -> bool> DoubleEndedIterator
    for FilterIterator<Iter, F>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        proof { use_type_invariant(&*self); }
        match self.state.take() {
            None => None,
            Some(state) => {
                let (state, ret) = state.next_back();
                self.state = Some(state);
                ret
            },
        }
    }
}

impl<Iter: DoubleEndedIterator, F: FnMut(&Iter::Item) -> bool>
    vstd::std_specs::iter::DoubleEndedIteratorSpecImpl for FilterIterator<Iter, F>
{
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        None
    }
}

fn map_from_both_ends() {
    let input = vec![1u32, 2, 3, 4];
    let mut iter = MapIterator::new(
        input.into_iter(),
        |x: u32| -> (out: u32)
            requires x < 10,
            ensures out == x + 10,
        { x + 10 },
    );
    let len = iter.len();
    assert(len == 4);
    let back = iter.next_back();
    assert(back == Some(14));
    let len = iter.len();
    assert(len == 3);
    let front = iter.next();
    assert(front == Some(11));
    let len = iter.len();
    assert(len == 2);
    let back = iter.next_back();
    assert(back == Some(13));
    let front = iter.next();
    assert(front == Some(12));
    let len = iter.len();
    assert(len == 0);
    let back = iter.next_back();
    assert(back == None);
    let front = iter.next();
    assert(front == None);
}

fn filter_from_both_ends() {
    let input = vec![1u32, 2];
    let mut iter = FilterIterator::new(
        input.into_iter(),
        |x: &u32| -> (keep: bool)
            ensures keep == (*x % 2 == 0),
        { *x % 2 == 0 },
    );
    let back = iter.next_back();
    assert(back == Some(2)) by { reveal_with_fuel(Seq::filter_index, 3); }
    let front = iter.next();
    assert(front == None) by { reveal_with_fuel(Seq::filter_index, 3); }
    let back = iter.next_back();
    assert(back == None);
}

fn filter_rejects_from_back() {
    let input = vec![2u32, 3];
    let mut iter = FilterIterator::new(
        input.into_iter(),
        |x: &u32| -> (keep: bool)
            ensures keep == (*x % 2 == 0),
        { *x % 2 == 0 },
    );
    let front = iter.next();
    assert(front == Some(2)) by { reveal_with_fuel(Seq::filter_index, 3); }
    let back = iter.next_back();
    assert(back == None) by { reveal_with_fuel(Seq::filter_index, 3); }
    let front = iter.next();
    assert(front == None);
}

} // verus!
