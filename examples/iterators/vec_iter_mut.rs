#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::proph::*;
use vstd::predicate::*;
use vstd::modes::*;
use vstd::std_specs::iter::IteratorSpec;

verus! {

// Proph lib

tracked struct ProphecyGhostConstrained<T, Pred: Predicate<T>> {
    ghost pred: Pred,
    tracked inner: ProphecyGhost<T>,
}

impl<T, Pred: Predicate<T>> ProphecyGhostConstrained<T, Pred> {
    pub closed spec fn pred(self) -> Pred {
        self.pred
    }

    #[verifier::prophetic]
    pub closed spec fn value(&self) -> T {
        if self.pred.predicate(self.inner.value()) {
            self.inner.value()
        } else {
            choose|v| self.pred.predicate(v)
        }
    }

    pub closed spec fn wf(self) -> bool {
        exists |v| self.pred.predicate(v)
    }

    pub proof fn new(witness: T, pred: Pred) -> (tracked proph_var: Self)
        requires pred.predicate(witness)
        ensures proph_var.wf(), proph_var.pred() == pred,
    {
        ProphecyGhostConstrained {
            pred: pred,
            inner: ProphecyGhost::<T>::new(),
        }
    }

    pub proof fn resolve(tracked self, value: T)
        requires self.wf(),
            self.pred().predicate(value)
        ensures
            self.value() == value,
    {
        self.inner.resolve(value);
    }
}

broadcast proof fn prophecy_ghost_constrained_satisfies<T, Pred: Predicate<T>>
    (p: ProphecyGhostConstrained::<T, Pred>)
    requires #[trigger] p.wf(),
    ensures p.pred().predicate(p.value())
{
}

// Proph lib, vec

/*
pub trait IndexPredicate<V> {
    spec fn predicate(&self, v: V, i: nat) -> bool;
}

pub open spec fn exists_witness<V, Pred: IndexPredicate<V>>(p: Pred, i: nat) -> bool {
    exists |v| p.predicate(v, i)
}

tracked struct ProphecyGhostConstrainedSeq<T, Pred: IndexPredicate<T>> {
    ghost pred: Pred,
    ghost history: Seq<T>,
    tracked inner: ProphecySeq<T>,
}

impl<T, Pred: IndexPredicate<T>> ProphecyGhostConstrainedSeq<T, Pred> {
    pub closed spec fn pred(self) -> Pred {
        self.pred
    }

    #[verifier::prophetic]
    pub closed spec fn value(&self, i: nat) -> T {
        if i < self.history.len() {
            self.history[i as int]
        } else if self.pred.predicate(self.inner.seq()[i - self.history.len()], i) {
            self.inner.seq()[i - self.history.len()]
        } else {
            choose |x| self.pred.predicate(x, i)
        }
    }

    pub closed spec fn index(self) -> nat {
        self.history.len()
    }

    pub closed spec fn wf(self) -> bool {
        forall |i: nat| exists_witness(self.pred, i)
    }

    pub proof fn new(pred: Pred) -> (tracked proph_var: Self)
        requires forall |i| exists_witness(pred, i)
        ensures proph_var.wf(), proph_var.pred() == pred,
    {
        ProphecyGhostConstrainedSeq {
            pred: pred,
            history: seq![],
            inner: ProphecySeq::<T>::new(),
        }
    }

    pub proof fn resolve_cons(tracked &mut self, value: T)
        requires self.wf(),
            self.pred().predicate(value, self.index())
        ensures
            final(self).wf(),
            forall |i| #![all_triggers] final(self).value(i) == old(self).value(i),
            final(self).index() == old(self).index() + 1,
    {
        self.history = self.history.push(value);
        self.inner.resolve_cons(value);
        assert forall |i| #![all_triggers] final(self).value(i) == old(self).value(i) by {
            assert(exists_witness(self.pred, i));
            if i < self.history.len() {
                assert(final(self).value(i) == old(self).value(i));
            } else if self.pred.predicate(self.inner.seq()[i - self.history.len()], i) {
                assert(self.inner.seq()[i - self.history.len()]
                    == old(self).inner.seq()[i - self.history.len() + 1]);
                assert(final(self).value(i) == old(self).value(i));
            } else {
                assert(final(self).value(i) == old(self).value(i));
            }
        }
    }
}

broadcast proof fn prophecy_ghost_seq_constrained_satisfies<T, Pred: IndexPredicate<T>>
    (p: ProphecyGhostConstrainedSeq::<T, Pred>, i: nat)
    requires p.wf(),
    ensures p.pred().predicate(#[trigger] p.value(i), i)
{
    assert(exists_witness(p.pred(), i));
}
*/

pub trait IndexPredicate<V> {
    #[verifier::prophetic]
    spec fn predicate(&self, v: V, i: nat) -> bool;
}

#[verifier::prophetic]
pub open spec fn exists_witness<V, Pred: IndexPredicate<V>>(p: Pred, i: nat) -> bool {
    exists |v| p.predicate(v, i)
}

// TODO: workaround
type SpecFnNat<T> = spec_fn(nat) -> T;

tracked struct ProphecyGhostConstrainedSeq<T, Pred: IndexPredicate<T>> {
    ghost pred: Pred,
    ghost history: Seq<T>,
    tracked inner: ProphecyGhost< SpecFnNat<T> >,
}

impl<T, Pred: IndexPredicate<T>> ProphecyGhostConstrainedSeq<T, Pred> {
    pub closed spec fn pred(self) -> Pred {
        self.pred
    }

    #[verifier::prophetic]
    pub closed spec fn value(&self, i: nat) -> T {
        if i < self.history.len() {
            self.history[i as int]
        } else if self.pred.predicate(self.inner.value()(i), i) {
            self.inner.value()(i)
        } else {
            choose |x| self.pred.predicate(x, i)
        }
    }

    pub closed spec fn index(self) -> nat {
        self.history.len()
    }

    #[verifier::prophetic]
    pub closed spec fn wf(self) -> bool {
        &&& forall |i: nat| exists_witness(self.pred, i)
        &&& forall |i: nat| #![all_triggers] 0 <= i < self.history.len() ==> self.pred.predicate(self.history[i as int], i)
    }

    pub proof fn new(pred: Pred) -> (tracked proph_var: Self)
        requires forall |i| exists_witness(pred, i)
        ensures proph_var.wf(), proph_var.pred() == pred, proph_var.index() == 0,
    {
        ProphecyGhostConstrainedSeq {
            pred: pred,
            history: seq![],
            inner: ProphecyGhost::<SpecFnNat<T>>::new(),
        }
    }

    pub proof fn resolve_cons(tracked &mut self, value: T)
        requires self.wf(),
            self.pred().predicate(value, self.index())
        ensures
            final(self).value(old(self).index()) == value,
            final(self).wf(),
            final(self).pred() == old(self).pred(),
            forall |i| #![all_triggers] final(self).value(i) == old(self).value(i),
            final(self).index() == old(self).index() + 1,
    {
        let tracked mut var = ProphecyGhost::new();
        tracked_swap(&mut var, &mut self.inner);
        var.resolve_dependent(&self.inner, |w| fn_set(w, self.history.len(), value));

        self.history = self.history + seq![value];
    }
}

spec fn fn_set<T>(w: spec_fn(nat) -> T, i: nat, t: T) -> spec_fn(nat) -> T {
    |j| if i == j { t } else { w(j) }
}

broadcast proof fn prophecy_ghost_seq_constrained_satisfies<T, Pred: IndexPredicate<T>>
    (p: ProphecyGhostConstrainedSeq::<T, Pred>, i: nat)
    requires p.wf(),
    ensures p.pred().predicate(#[trigger] p.value(i), i)
{
    assert(exists_witness(p.pred(), i));
}

// SliceIterMut

ghost struct SliceIterMutPred<'a, T> {
    slice: &'a mut [T],
}

impl<'a, T> IndexPredicate<&'a mut T> for SliceIterMutPred<'a, T> {
    #[verifier::prophetic]
    closed spec fn predicate(&self, v: &'a mut T, i: nat) -> bool {
        i < self.slice.len() ==>
            *v == (*self.slice)[i as int] && *final(v) == (*final(self.slice))[i as int]
    }
}

struct SliceIterMut<'a, T> {
    slice: &'a mut [T],
    proph: Tracked<ProphecyGhostConstrainedSeq<&'a mut T, SliceIterMutPred<'a, T>>>,
    index: Ghost<int>,
}

// Perhaps there should just be an axiom that
// `exists |proph_var: ProphecyGhost<T>| proph_var.value() == s`
// but this is inconsistent with the VerusBelt model of `ProphecyGhost<T>` as an integer
// (which is currently exposed via ProphecyGhost being marked allow_recursive)
proof fn prove_exists_witness<T>(pred: SliceIterMutPred<T>, j: nat, tracked t: &&mut [T])
    requires pred.slice == *t
    ensures forall |i: nat| 0 <= i < j ==> exists_witness(pred, i)
    decreases j
{
    if j == 0 {
    } else {
        let k = (j-1) as nat;
        prove_exists_witness(pred, k, t);

        let tracked g = ProphecyGhost::<&T>::new();
        g.resolve_dependent(vstd::mut_ref::borrow_prophecy_var(t), |s: &[T]| &s[k as int]);
        let v_unpacked = vstd::mut_ref::MutRef {
            ptr: arbitrary(),
            current: &t[k as int],
            future: g,
        };
        let v = v_unpacked.pack();
        assert(pred.predicate(v, k));
    }
}

impl<'a, T> SliceIterMut<'a, T> {
    fn new(s: &'a mut [T]) -> (out: Self)
        ensures
            old(s).len() == final(s).len(),
            out.remaining().len() == old(s).len(),
            out.will_return_none(),
            forall |i| #![all_triggers] 0 <= i < old(s).len() ==>
                *out.remaining()[i] == old(s)[i] && *final(out.remaining()[i]) == final(s)[i],
    {
        let tracked proph_var;
        proof {
            let pred = SliceIterMutPred { slice: s };
            prove_exists_witness(pred, s@.len(), &s);
            vstd::slice::mut_ref_slice_len_eq(&s);
            assert forall |i| exists_witness(pred, i) by {
                if i < s@.len() {
                    assert(exists_witness(pred, i));
                } else {
                    assert(pred.predicate(arbitrary(), i));
                }
            }
            proph_var = ProphecyGhostConstrainedSeq::new(pred);

            broadcast use prophecy_ghost_seq_constrained_satisfies;
            //assert forall |i| #![all_triggers] 0 <= i < old(s).len() implies
            //    *proph_var.value(i as nat) == old(s)[i] && *final(proph_var.value(i as nat)) == final(s)[i]
            //by {
            //}
        }

        SliceIterMut {
            proph: Tracked(proph_var),
            slice: s,
            index: Ghost(0),
        }
    }

    #[verifier::type_invariant]
    #[verifier::prophetic]
    spec fn slice_iter_mut_wf(self) -> bool {
        self.proph.wf()
            && self.proph.pred().slice.len() == self.slice.len() + self.index@
            && self.proph.index() == self.index@
            && (forall |i| #![all_triggers] 0 <= i < self.slice.len() ==>
                    self.slice[i] == self.proph.pred().slice[i + self.index@]
                    && final(self.slice)[i] == final(self.proph.pred().slice)[i + self.index@]
            )
    }
}

impl<'a, T> Iterator for SliceIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        proof { use_type_invariant(&*self); }
        Self::next_inner(&mut self.slice, Tracked(&mut self.proph), Tracked(&mut self.index))
    }
}

impl<'a, T> SliceIterMut<'a, T> {
    fn next_inner(
        slice: &mut &'a mut [T],
        Tracked(proph): Tracked<&mut Tracked<ProphecyGhostConstrainedSeq<&'a mut T, SliceIterMutPred<'a, T>>>>,
        Tracked(index): Tracked<&mut Ghost<int>>,
    ) -> (out: Option<&'a mut T>)
        requires SliceIterMut::slice_iter_mut_wf(SliceIterMut { slice: *slice, proph: *proph, index: *index })
        ensures SliceIterMut::slice_iter_mut_wf(SliceIterMut { slice: *final(slice), proph: *final(proph), index: *final(index) }),
            old(*old(slice)).len() == 0 ==> old(*final(slice)).len() == 0 && out.is_none(),
            old(*old(slice)).len() > 0 ==> old(*final(slice)).len() + 1 == old(*old(slice)).len(),
            old(*old(slice)).len() > 0 ==>
                Self::remaining_inner(&SliceIterMut { slice: *final(slice), proph: *final(proph), index: *final(index) }) =~=
                Self::remaining_inner(&SliceIterMut { slice: *old(slice), proph: *old(proph), index: *old(index) }).drop_first(),
            old(*old(slice)).len() > 0 ==>
              out == Some(Self::remaining_inner(&SliceIterMut { slice: *old(slice), proph: *old(proph), index: *old(index) })[0])
        no_unwind
    {
        let mut s: &mut [T] = &mut [];
        std::mem::swap(slice, &mut s);
        match s.split_first_mut() {
            None => {
                None
            }
            Some((first, rest)) => {
                *slice = rest;
                let x = Some(first);
                proof {
                    proph.resolve_cons(x->Some_0);
                    *index = Ghost(**index + 1);
                }
                x
            }
        }
    }

    #[verifier::prophetic]
    spec fn remaining_inner(&self) -> Seq<&'a mut T> {
        Seq::new(self.slice@.len(), |i: int| self.proph.value((self.index@ + i) as nat))
    }
}

impl<'a, T> vstd::std_specs::iter::IteratorSpecImpl for SliceIterMut<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        self.remaining_inner()
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        true
    }

    closed spec fn decrease(&self) -> Option<nat> {
        Some(self.slice.len() as nat)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

} // verus!
