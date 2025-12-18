use super::super::prelude::*;

use verus as verus_;

use core::iter::Iterator;

verus_! {

#[verifier::external_trait_specification]
pub trait ExIntoIterator {
    type ExternalTraitSpecificationFor: core::iter::IntoIterator;
}

#[verifier::external_trait_specification]
pub trait ExIterStep: Clone + PartialOrd + Sized {
    type ExternalTraitSpecificationFor: core::iter::Step;
}

/*
#[verifier::external_trait_specification]
pub trait ExIterator {
    type ExternalTraitSpecificationFor: core::iter::Iterator;

    type Item;

    fn next(&mut self) -> Option<Self::Item>;
}
*/

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IteratorSpec via IteratorSpecImpl)]
pub trait ExIterator {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    /// This iterator obeys the specifications below on `next`
    spec fn obeys_iter_laws(&self) -> bool;

    /// Sequence of items that will (eventually) be returned
    #[verifier::prophetic]
    spec fn seq(&self) -> Seq<Self::Item>;

    /// Does this iterator complete with a `None` after the above sequence?
    /// (As opposed to hanging indefinitely on a `next()` call)
    /// Trivially true for most iterators but important for iterators
    /// that apply an exec closure that may not terminate.
    #[verifier::prophetic]
    spec fn completes(&self) -> bool;

    /// Advances the iterator and returns the next value.
    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            // The iterator consistently obeys, completes, and decreases throughout its lifetime
            self.obeys_iter_laws() == old(self).obeys_iter_laws(),
            self.obeys_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_iter_laws() ==> (old(self).decrease() is Some <==> self.decrease() is Some),
            // `next` pops the head of the prophesized seq(), or returns None
            self.obeys_iter_laws() ==> 
            ({
                if old(self).seq().len() > 0 {
                    &&& self.seq() == old(self).seq().drop_first()
                    &&& ret == Some(old(self).seq()[0])
                } else {
                    self.seq() === old(self).seq() && ret === None && self.completes()
                }
            }),
            // If the iterator isn't done yet, then it successfully decreases its metric (if any)
            self.obeys_iter_laws() && old(self).seq().len() > 0 && self.decrease() is Some ==> 
                decreases_to!(old(self).decrease()->0 => self.decrease()->0),
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
    spec fn initial_value_inv(&self, init: Option<&Self>) -> bool;
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

    /// Bundle the real iterator with its ghost state and loop invariants
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

    /// Advance the underlying (real) iterator and prove
    /// that the loop invariants are preserved.
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
                decreases_to!(old(self).iter.decrease()->0 => self.iter.decrease()->0),
    {
        let ret = self.iter.next();
        proof {
            if ret.is_some() {
                self.index@ = self.index@ + 1;
            }
        }
// TODO:
assume(false);
        ret
    }
}


/*
pub struct VerusForLoopIterator<'a, I: Iterator> {
    pub index: Ghost<int>,
    pub snapshot: Ghost<I>,
    pub init: Ghost<Option<&'a I>>,
    pub iter: I 
}

impl <'a, I: Iterator> VerusForLoopIterator<'a, I> {
    pub open spec fn seq(self) -> Seq<I::Item> {
        Seq::empty()
    }

    /// These properties help maintain the properties in wf,
    /// but they don't need to be exposed to the client 
    #[verifier::prophetic]
    pub closed spec fn wf_inner(self) -> bool {
        true
    }

    /// These properties are needed for the client code to verify
    #[verifier::prophetic]
    pub open spec fn wf(self) -> bool {
        true
    }

    /// Bundle the real iterator with its ghost state and loop invariants
    pub fn new(iter: I, init: Ghost<Option<&'a I>>) -> (s: Self)
    {
        VerusForLoopIterator {
            index: Ghost(0),
            snapshot: Ghost(iter),
            init: init,
            iter,
        }
    }

    /// Advance the underlying (real) iterator and prove
    /// that the loop invariants are preserved.
    pub fn next(&mut self) -> (ret: Option<I::Item>)
    {
        None
    }
}
*/
} // verus!
