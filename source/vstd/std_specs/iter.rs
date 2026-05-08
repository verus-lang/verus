use super::super::prelude::*;
use super::super::seq::{
    axiom_seq_empty, axiom_seq_subrange_index, axiom_seq_subrange_len, group_seq_axioms,
};

use verus as verus_;

use core::iter::{Iterator, Rev};

verus_! {

#[verifier::external_trait_specification]
pub trait ExIntoIterator {
    type ExternalTraitSpecificationFor: core::iter::IntoIterator;
}


#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IteratorSpec via IteratorSpecImpl)]
pub trait ExIterator {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    /// This iterator obeys the specifications below on `next`,
    /// expressed in terms of prophetic spec functions.
    /// Only iterators that terminate (i.e., eventually return None
    /// and then continue to return None) should use this interface.
    spec fn obeys_prophetic_iter_laws(&self) -> bool;

    /// Sequence of items that will (eventually) be returned
    #[verifier::prophetic]
    spec fn remaining(&self) -> Seq<Self::Item>;

    /// Does this iterator complete with a `None` after the above sequence?
    /// (As opposed to hanging indefinitely on a `next()` call)
    /// Trivially true for most iterators but important for iterators
    /// that apply an exec closure that may not terminate.
    #[verifier::prophetic]
    spec fn will_return_none(&self) -> bool;

    /// Advances the iterator and returns the next value.
    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            // The iterator consistently obeys, completes, and decreases throughout its lifetime
            final(self).obeys_prophetic_iter_laws() == old(self).obeys_prophetic_iter_laws(),
            final(self).obeys_prophetic_iter_laws() ==> final(self).will_return_none() == old(self).will_return_none(),
            final(self).obeys_prophetic_iter_laws() ==> (old(self).decrease() is Some <==> final(self).decrease() is Some),
            // `next` pops the head of the prophesized remaining(), or returns None
            final(self).obeys_prophetic_iter_laws() ==>
            ({
                if old(self).remaining().len() > 0 {
                    &&& final(self).remaining() == old(self).remaining().drop_first()
                    &&& ret == Some(old(self).remaining()[0])
                } else {
                    final(self).remaining() === old(self).remaining() && ret === None && final(self).will_return_none()
                }
            }),
            // If the iterator isn't done yet, then it successfully decreases its metric (if any)
            final(self).obeys_prophetic_iter_laws() && old(self).remaining().len() > 0 && final(self).decrease() is Some ==>
                decreases_to!(old(self).decrease()->0 => final(self).decrease()->0),
    ;

    /******* Mechanisms that support ergonomic `for` loops *********/

    /// Value used by default for the decreases clause when no explicit decreases clause is provided
    /// (the user can override this with an explicit decreases clause).
    /// If there's no appropriate metric to decrease, this can return None,
    /// and the user will have to provide an explicit decreases clause.
    spec fn decrease(&self) -> Option<nat>;

    /// Invariant relating the iterator to the initial expression that created it
    /// (e.g., `my_vec.iter()`).  This allows for more ergonomic/intuitive invariants.
    /// When the analysis can infer a spec initial value (by discovering a `when_used_as_spec`
    /// annotation), the analysis places the value in init.
    #[verifier::prophetic]
    spec fn initial_value_relation(&self, init: &Self) -> bool;

    // If we can make a useful guess as to what the i-th value will be, return it.
    // Otherwise, return None.
    spec fn peek(&self, index: int) -> Option<Self::Item>;

    // Provided methods

    // TODO: Once we can add when_used_as_spec to provided trait methods, this would be a simpler encoding:
    //#[verifier::when_used_as_spec(into_rev_spec)]
    fn rev(self) -> (r: Rev<Self>)
        where Self: Sized,
        default_ensures
            self.obeys_prophetic_iter_laws() && self.initial_value_relation(&self) ==>
                r == into_rev_spec(self) && rev_post(self, r),
    ;

}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(DoubleEndedIteratorSpec via DoubleEndedIteratorSpecImpl)]
pub trait ExDoubleEndedIterator : Iterator {
    type ExternalTraitSpecificationFor: DoubleEndedIterator;

    // In the specs below, we write out the type parameters explicitly, rather than using the more concise form,
    // e.g., `final(self).obeys_prophetic_iter_laws()`.  If we use the latter, then Rust elaborates it to
    // `(&final(self)).obeys_prophetic_iter_laws()`, which means the type of the argument is `& &mut Self`,
    // which means the type argument inferred for `obeys_prophetic_iter_laws` is `&mut Self`.
    // This happens because of the existing Rust [trait impl](https://doc.rust-lang.org/std/iter/trait.Iterator.html#impl-Iterator-for-%26mut+I):
    // ```
    // impl<I> Iterator for &mut I
    // where
    //     I: Iterator + ?Sized,[4:21 AM]
    // ```
    fn next_back(&mut self) -> (ret: Option<<Self as core::iter::Iterator>::Item>)
        ensures
            // The iterator consistently obeys, completes, and decreases throughout its lifetime
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) == <Self as IteratorSpec>::obeys_prophetic_iter_laws(old(self)),
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) ==> <Self as IteratorSpec>::will_return_none(final(self)) == <Self as IteratorSpec>::will_return_none(old(self)),
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) ==> (<Self as IteratorSpec>::decrease(old(self)) is Some <==> <Self as IteratorSpec>::decrease(final(self)) is Some),
            // `next` pops the tail of the prophesized remaining(), or returns None
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) ==>
            ({
                if <Self as IteratorSpec>::remaining(old(self)).len() > 0 {
                    <Self as IteratorSpec>::remaining(final(self)) == <Self as IteratorSpec>::remaining(old(self)).drop_last()
                        && ret == Some(<Self as IteratorSpec>::remaining(old(self)).last())
                } else {
                    <Self as IteratorSpec>::remaining(final(self)) === <Self as IteratorSpec>::remaining(old(self)) && ret === None && <Self as IteratorSpec>::will_return_none(final(self))
                }
            }),
            // If the iterator isn't done yet, then it successfully decreases its metric (if any)
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) && <Self as IteratorSpec>::remaining(old(self)).len() > 0 && <Self as IteratorSpec>::decrease(final(self)) is Some ==>
                <Self as IteratorSpec>::decrease(old(self))->0 > <Self as IteratorSpec>::decrease(final(self))->0,
    ;

    /******* Mechanisms that support ergonomic `for` loops *********/

    // If we can make a useful guess as to what the i-th value from the back will be, return it.
    // Otherwise, return None.
    spec fn peek_back(&self, index: int) -> Option<Self::Item>;
}

/********************************************************************************
 * Definitions for `rev()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
pub struct ExRev<I>(Rev<I>);

// Ghost accessor for the inner iterator
pub uninterp spec fn rev_iter<I>(r: Rev<I>) -> I;

// Spec version of Rev::new
pub uninterp spec fn into_rev_spec<I>(i: I) -> Rev<I>;

// Ideally, we would write this postcondition directly on the definition of
// Iterator::rev above.  However, to do so, we would need to impose a trait
// bound of `Self: DoubleEndedIteratorSpec`.  However, this introduces a cyclic
// dependency, since DoubleEndedIteratorSpec depends on Iterator.  Hence,
// we introduce a layer of indirection via this uninterp spec function.
pub uninterp spec fn rev_post<I>(i: I, r: Rev<I>) -> bool;

pub broadcast axiom fn rev_postcondition<I: DoubleEndedIteratorSpec>(i: I)
    requires
        i.obeys_prophetic_iter_laws(),
        i.initial_value_relation(&i),
        rev_post(i, into_rev_spec(i)),
    ensures
        {
            let r = #[trigger] into_rev_spec(i);
            &&& IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse()
            &&& IteratorSpec::will_return_none(&r) == i.will_return_none()
            &&& IteratorSpec::decrease(&r) is Some == i.decrease() is Some
            &&& IteratorSpec::initial_value_relation(&r, &r)
        },
;

impl <I> IteratorSpecImpl for Rev<I>
    where I: DoubleEndedIterator + DoubleEndedIteratorSpec {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        rev_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        rev_iter(*self).remaining().reverse()
    }

    #[verifier::prophetic]
    closed spec fn will_return_none(&self) -> bool {
        rev_iter(*self).will_return_none()
    }

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& rev_iter(*self).initial_value_relation(&rev_iter(*init))
    }

    closed spec fn decrease(&self) -> Option<nat> {
        rev_iter(*self).decrease()
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        rev_iter(*self).peek_back(index)
    }
}

impl <I> DoubleEndedIteratorSpecImpl for Rev<I>
    where I: DoubleEndedIterator + IteratorSpec {

    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        rev_iter(*self).peek(index)
    }
}

/********************************************************************************
 * Defines a convenient wrapper type that bundles state and invariants needed
 * for ergonomic for-loop support.
 ********************************************************************************/

pub struct VerusForLoopWrapper<'a, I: Iterator> {
    pub index: Ghost<int>,
    pub snapshot: Ghost<I>,
    pub init: Ghost<Option<&'a I>>,
    pub iter: I,
    pub history: Ghost<Seq<I::Item>>,
}

impl <'a, I: Iterator> VerusForLoopWrapper<'a, I> {
    #[verifier::prophetic]
    pub open spec fn seq(self) -> Seq<I::Item> {
        self.snapshot@.remaining()
    }

    // Keep the interface for history and seq the same
    pub open spec fn history(self) -> Seq<I::Item> {
        self.history@
    }

    pub open spec fn index(self) -> int {
        self.index@
    }

    /// These properties help maintain the properties in wf,
    /// but they don't need to be exposed to the client
    #[verifier::prophetic]
    pub closed spec fn wf_inner(self) -> bool {
        &&& self.iter.remaining().len() == self.seq().len() - self.index()
        &&& forall |i| 0 <= i < self.iter.remaining().len() ==> #[trigger] self.iter.remaining()[i] == self.seq()[self.index() + i]
        &&& self.iter.will_return_none() ==> self.snapshot@.will_return_none()
    }

    /// These properties are needed for the client code to verify
    #[verifier::prophetic]
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.index() <= self.seq().len()
        &&& self.init@ matches Some(init) ==> self.snapshot@.initial_value_relation(init)
        &&& self.wf_inner()
        &&& self.iter.obeys_prophetic_iter_laws() ==> {
                &&& self.history@.len() == self.index()
                &&& forall |i| 0 <= i < self.index() ==> #[trigger] self.history@[i] == self.seq()[i]
            }
    }

    /// Bundle the real iterator with its ghost state and loop invariants
    pub fn new(iter: I, init: Ghost<Option<&'a I>>) -> (s: Self)
        requires
            init@ matches Some(i) ==> iter.initial_value_relation(i),
        ensures
            s.index == 0,
            s.snapshot == iter,
            s.init == init,
            s.iter == iter,
            s.history@ == Seq::<I::Item>::empty(),
            s.wf(),
    {
        broadcast use axiom_seq_empty;
        VerusForLoopWrapper {
            index: Ghost(0),
            snapshot: Ghost(iter),
            init: init,
            iter,
            history: Ghost(Seq::empty()),
        }
    }

    /// Advance the underlying (real) iterator and prove
    /// that the loop invariants are preserved.
    pub fn next(&mut self) -> (ret: Option<I::Item>)
        requires
            old(self).wf(),
        ensures
            final(self).seq() == old(self).seq(),
            final(self).index() == old(self).index() + if ret is Some { 1int } else { 0 },
            final(self).snapshot == old(self).snapshot,
            final(self).init == old(self).init,
            final(self).iter.obeys_prophetic_iter_laws() ==> final(self).wf(),
            final(self).iter.obeys_prophetic_iter_laws() && ret is None ==>
                final(self).snapshot@.will_return_none() && final(self).index() == final(self).seq().len(),
            final(self).iter.obeys_prophetic_iter_laws() ==> (ret matches Some(r) ==>
                r == old(self).seq()[old(self).index()]),
            // History updates always hold
            ret matches Some(i) ==> final(self).history@ == old(self).history@.push(i),
            ret is None ==> final(self).history@ == old(self).history@,
            // TODO: Uncomment this line to replace everything below, once general mutable refs are supported
            //call_ensures(I::next, (old(self).iter,), ret),
            final(self).iter.obeys_prophetic_iter_laws() == old(self).iter.obeys_prophetic_iter_laws(),
            final(self).iter.obeys_prophetic_iter_laws() ==> final(self).iter.will_return_none() == old(self).iter.will_return_none(),
            final(self).iter.obeys_prophetic_iter_laws() ==> (old(self).iter.decrease() is Some <==> final(self).iter.decrease() is Some),
            final(self).iter.obeys_prophetic_iter_laws() ==>
            ({
                if old(self).iter.remaining().len() > 0 {
                    &&& final(self).iter.remaining() == old(self).iter.remaining().drop_first()
                    &&& ret == Some(old(self).iter.remaining()[0])
                } else {
                    final(self).iter.remaining() === old(self).iter.remaining() && ret === None && final(self).iter.will_return_none()
                }
            }),
            final(self).iter.obeys_prophetic_iter_laws() && old(self).iter.remaining().len() > 0 && final(self).iter.decrease() is Some ==>
                decreases_to!(old(self).iter.decrease()->0 => final(self).iter.decrease()->0),
    {
        let ghost old_history = self.history@;
        let ret = self.iter.next();
        if ret.is_some() {
            self.history = Ghost(old_history.push(ret->0));
        }
        proof {
            broadcast use group_seq_axioms;
            if ret.is_some() {
                self.index@ = self.index@ + 1;
            }
        }
        ret
    }
}

// Artificial function used when we desguar a for loop.
// It helps bring the definition of `peek` into scope,
// resulting in better automation for some proofs.
pub open spec fn trigger_peek_implications<T>(x: T) -> bool { true }

/********************************************************************************
 * Definitions for the Step trait
 ********************************************************************************/
#[verifier::external_trait_specification]
#[verifier::external_trait_extension(StepSpec via StepSpecImpl)]
pub trait ExIterStep: Clone + PartialOrd + Sized {
    type ExternalTraitSpecificationFor: core::iter::Step;

    // REVIEW: it would be nice to be able to use SpecOrd::spec_lt (not yet supported)
    // TODO: We should now be able to use cmp_spec or partial_cmp_spec here.
    spec fn spec_is_lt(self, other: Self) -> bool;

    spec fn spec_steps_between(self, end: Self) -> Option<usize>;

    spec fn spec_steps_between_int(self, end: Self) -> int;

    spec fn spec_forward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_forward_checked_int(self, count: int) -> Option<Self>;

    spec fn spec_backward_checked(self, count: usize) -> Option<Self>;

    spec fn spec_backward_checked_int(self, count: int) -> Option<Self>;
}


/********************************************************************************
 * Collect our broadcast definitions
 ********************************************************************************/

pub broadcast group group_iter_axioms {
    rev_postcondition,
}

} // verus!
