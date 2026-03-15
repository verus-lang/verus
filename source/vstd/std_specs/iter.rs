use super::super::prelude::*;
use super::super::seq::{
    axiom_seq_empty, axiom_seq_subrange_index, axiom_seq_subrange_len, group_seq_axioms,
};

use verus as verus_;

use core::iter::{Filter, FromIterator, Iterator, Rev};

verus_! {

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
    spec fn completes(&self) -> bool;

    /// Advances the iterator and returns the next value.
    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            // The iterator consistently obeys, completes, and decreases throughout its lifetime
            self.obeys_prophetic_iter_laws() == old(self).obeys_prophetic_iter_laws(),
            self.obeys_prophetic_iter_laws() ==> self.completes() == old(self).completes(),
            self.obeys_prophetic_iter_laws() ==> (old(self).decrease() is Some <==> self.decrease() is Some),
            // `next` pops the head of the prophesized remaining(), or returns None
            self.obeys_prophetic_iter_laws() ==>
            ({
                if old(self).remaining().len() > 0 {
                    &&& self.remaining() == old(self).remaining().drop_first()
                    &&& ret == Some(old(self).remaining()[0])
                } else {
                    self.remaining() === old(self).remaining() && ret === None && self.completes()
                }
            }),
            // If the iterator isn't done yet, then it successfully decreases its metric (if any)
            self.obeys_prophetic_iter_laws() && old(self).remaining().len() > 0 && self.decrease() is Some ==>
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
    #[verifier::prophetic]
    spec fn initial_value_inv(&self, init: &Self) -> bool;

    // If we can make a useful guess as to what the i-th value will be, return it.
    // Otherwise, return None.
    spec fn peek(&self, index: int) -> Option<Self::Item>;

    // Provided methods

    // TODO: Pending a resolution of https://github.com/verus-lang/verus/issues/2236
    // //#[verifier::when_used_as_spec(into_map_spec)]
    // fn map<B, F>(self, f: F) -> (r: core::iter::Map<Self, F>)
    //     where
    //         Self: Sized,
    //         F: FnMut(Self::Item) -> B,
    //     requires
    //         self.obeys_prophetic_iter_laws(),
    //         forall |k| #![auto] 0 <= k < self.remaining().len() ==> call_requires(f, (self.remaining()[k], )),
    //         self.initial_value_inv(&self),
    //     default_ensures
    //     // TODO:
    //         //r == into_map_spec::<B, I, F>(self, f),
    //         IteratorSpec::remaining(&r).len() <= self.remaining().len(),
    //         forall |k| #![auto] 0 <= k < IteratorSpec::remaining(&r).len() ==> call_ensures(f, (self.remaining()[k],), IteratorSpec::remaining(&r)[k]),
    //         IteratorSpec::completes(&r) ==> self.completes() &&
    //             IteratorSpec::remaining(&r).len() == self.remaining().len(),
    //         IteratorSpec::decrease(&r) is Some == self.decrease() is Some,
    //         IteratorSpec::initial_value_inv(&r, &r),
    //         map_iter(r) == self,
    //         map_fun(r) == f,
    // ;

    //#[verifier::when_used_as_spec(into_rev_spec)]
    fn rev(self) -> (r: Rev<Self>)
        where Self: Sized,
        requires
            self.obeys_prophetic_iter_laws(),   // REVIEW: Should this be moved to an implication on the ensures clauses?
            self.initial_value_inv(&self),
        default_ensures
            r == into_rev_spec(self),
            rev_post(self, r),
    ;

    fn filter<P>(self, pred: P) -> (r: Filter<Self, P>)
        where Self: Sized, P: FnMut(&Self::Item) -> bool,
        requires
            self.obeys_prophetic_iter_laws(),
            forall |k: int| #![auto] 0 <= k < self.remaining().len() ==> call_requires(pred, (&self.remaining()[k],)),
            self.initial_value_inv(&self),
        default_ensures
            r == into_filter_spec(self, pred),
            filter_post(self, pred, r),
    ;

    fn collect<B>(self) -> (collection: B)
        where
            B: FromIterator<Self::Item>,
            Self: Sized,
        requires
            self.obeys_prophetic_iter_laws(),   // REVIEW: Should this be moved to an implication on the ensures clauses?
            B::obeys_from_iterator_spec(),
        default_ensures
            FromIteratorSpec::from_iter_ensures(self.remaining(), collection),
    ;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(DoubleEndedIteratorSpec via DoubleEndedIteratorSpecImpl)]
pub trait ExDoubleEndedIterator : Iterator {
    type ExternalTraitSpecificationFor: DoubleEndedIterator;

    // TODO: Remove the `(&*self)` notation once the new support for `&mut` lands
    //       At present, without it, we get "The verifier does not yet support the following Rust feature: &mut types, except in special cases"
    fn next_back(&mut self) -> (ret: Option<<Self as core::iter::Iterator>::Item>)
        ensures
            // The iterator consistently obeys, completes, and decreases throughout its lifetime
            (&*self).obeys_prophetic_iter_laws() == (&*old(self)).obeys_prophetic_iter_laws(),
            (&*self).obeys_prophetic_iter_laws() ==> (&*self).completes() == (&*old(self)).completes(),
            (&*self).obeys_prophetic_iter_laws() ==> ((&*old(self)).decrease() is Some <==> (&*self).decrease() is Some),
            // `next` pops the tail of the prophesized remaining(), or returns None
            (&*self).obeys_prophetic_iter_laws() ==>
            ({
                if (&*old(self)).remaining().len() > 0 {
                    (&*self).remaining() == (&*old(self)).remaining().drop_last()
                        && ret == Some((&*old(self)).remaining().last())
                } else {
                    (&*self).remaining() === (&*old(self)).remaining() && ret === None && (&*self).completes()
                }
            }),
            // If the iterator isn't done yet, then it successfully decreases its metric (if any)
            (&*self).obeys_prophetic_iter_laws() && (&*old(self)).remaining().len() > 0 && (&*self).decrease() is Some ==>
                (&*old(self)).decrease()->0 > (&*self).decrease()->0,
    ;

    /******* Mechanisms that support ergonomic `for` loops *********/

    // If we can make a useful guess as to what the i-th value from the back will be, return it.
    // Otherwise, return None.
    spec fn peek_back(&self, index: int) -> Option<Self::Item>;
}

/********************************************************************************
 * Definitions for `IntoIterator` and `FromIterator``
 ********************************************************************************/
#[verifier::external_trait_specification]
pub trait ExIntoIterator {
    type ExternalTraitSpecificationFor: core::iter::IntoIterator;
}
// Uninterpreted function representing the sequence of elements that will be
// produced by the iterator obtained from an IntoIterator value.
// This avoids requiring IteratorSpec bounds in from_iter's ensures clause.
pub uninterp spec fn into_iter_remaining<A, T>(iter: T) -> Seq<A>;

// Connects into_iter_remaining to remaining() for types implementing Iterator + IteratorSpec.
// This allows callers of from_iter to relate the result to the iterator's remaining elements.
pub broadcast axiom fn axiom_from_iterator_ensures<A, I: Iterator<Item = A> + IteratorSpec>(iter: I)
    ensures
        #[trigger] into_iter_remaining::<A, I>(iter) == iter.remaining(),
;

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FromIteratorSpec via FromIteratorSpecImpl)]
pub trait ExFromIterator<A>: Sized {
    type ExternalTraitSpecificationFor: FromIterator<A>;

    spec fn obeys_from_iterator_spec() -> bool;

    spec fn from_iter_ensures(remaining: Seq<A>, s: Self) -> bool;

    fn from_iter<T>(iter: T) -> (s: Self)
       where T: IntoIterator<Item = A>
        ensures
            Self::obeys_from_iterator_spec() ==> Self::from_iter_ensures(into_iter_remaining(iter), s),
    ;
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
        i.initial_value_inv(&i),
    ensures
        // TODO: Remove parens after we merge in main
        ({
            let r = #[trigger] into_rev_spec(i);
            &&& IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse()
            &&& IteratorSpec::completes(&r) == i.completes()
            &&& IteratorSpec::decrease(&r) is Some == i.decrease() is Some
            &&& IteratorSpec::initial_value_inv(&r, &r)
        }),
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
    closed spec fn completes(&self) -> bool {
        rev_iter(*self).completes()
    }

    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& rev_iter(*self).initial_value_inv(&rev_iter(*init))
        //&&& into_iter_elts(*self) == IteratorSpec::remaining(self)
        // TODO: More here?
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
 * Definitions for `filter()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(P)]
pub struct ExFilter<I, P>(Filter<I, P>);

// Ghost accessor for the inner iterator
pub uninterp spec fn filter_iter<I, P>(f: Filter<I, P>) -> I;

// Ghost accessor for the predicate
pub uninterp spec fn filter_pred<I, P>(f: Filter<I, P>) -> P;

// Spec version of Iterator::filter
pub uninterp spec fn into_filter_spec<I, P>(i: I, p: P) -> Filter<I, P>;

// Indirection for postcondition (avoids potential resolution issues at trait definition site)
pub uninterp spec fn filter_post<I, P>(i: I, p: P, r: Filter<I, P>) -> bool;

pub broadcast axiom fn filter_postcondition<I: IteratorSpec, P: FnMut(&<I as Iterator>::Item) -> bool>(i: I, p: P)
    requires
        filter_post(i, p, into_filter_spec(i, p)),
    ensures
        ({
            let r = #[trigger] into_filter_spec(i, p);
            &&& IteratorSpec::remaining(&r) == i.remaining().filter(
                    |item: <I as Iterator>::Item| call_ensures(p, (&item,), true)
                )
            &&& IteratorSpec::remaining(&r).len() <= i.remaining().len()
            &&& forall |k: int| #![auto] 0 <= k < IteratorSpec::remaining(&r).len() ==>
                    call_ensures(p, (&IteratorSpec::remaining(&r)[k],), true)
            &&& IteratorSpec::completes(&r) ==> i.completes()
            &&& IteratorSpec::decrease(&r) is Some == i.decrease() is Some
            &&& IteratorSpec::initial_value_inv(&r, &r)
        }),
;

impl<I, P> IteratorSpecImpl for Filter<I, P>
    where I: Iterator + IteratorSpec, P: FnMut(&I::Item) -> bool
{
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        filter_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        filter_iter(*self).remaining().filter(
            |item: I::Item| call_ensures(filter_pred::<I, P>(*self), (&item,), true)
        )
    }

    #[verifier::prophetic]
    closed spec fn completes(&self) -> bool {
        filter_iter(*self).completes()
    }

    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& filter_iter(*self).initial_value_inv(&filter_iter(*init))
    }

    closed spec fn decrease(&self) -> Option<nat> {
        filter_iter(*self).decrease()
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

/********************************************************************************
 * Definitions for `map()`
 ********************************************************************************/

// TODO: Pending a resolution of https://github.com/verus-lang/verus/issues/2236
// The external type specification and IteratorSpecImpl for core::iter::Map<I, F>
// are commented out because Verus's trait conflict checker reports that the type parameter
// B in std's Iterator and DoubleEndedIterator impls for Map is "not constrained by the
// impl trait, self type, or predicates". This is because those impls have an extra type
// parameter B (from F: FnMut(I::Item) -> B) that only appears in the where clause.
//
// #[verifier::external_body]
// #[verifier::external_type_specification]
// #[verifier::reject_recursive_types(I)]
// #[verifier::reject_recursive_types(F)]
// pub struct ExMap<I, F>(core::iter::Map<I, F>);
//
// // Ghost accessor for the inner iterator
// pub uninterp spec fn map_iter<I, F>(r: core::iter::Map<I, F>) -> I;
//
// // Ghost accessor for the inner function
// pub uninterp spec fn map_fun<I, F>(r: core::iter::Map<I, F>) -> F;
//
// The IteratorSpecImpl for core::iter::Map<I, F> is also commented out because
// Verus's type normalization panics when resolving <Map<I, F> as Iterator>::Item.
// The std Iterator impl for Map has an extra type parameter B (from F: FnMut(I::Item) -> B),
// and the normalizer introduces inference variables that trigger an assertion failure
// in rust_to_vir_base.rs.
//
// impl <B, I, F> IteratorSpecImpl for core::iter::Map<I, F>
//     where
//         I: Iterator + IteratorSpec,
//         F: FnMut(I::Item) -> B,
// {
//
//     open spec fn obeys_prophetic_iter_laws(&self) -> bool {
//         map_iter(*self).obeys_prophetic_iter_laws()
//     }
//
//     #[verifier::prophetic]
//     uninterp spec fn remaining(&self) -> Seq<Self::Item>;
//
//     #[verifier::prophetic]
//     uninterp spec fn completes(&self) -> bool;
//
//     #[verifier::prophetic]
//     open spec fn initial_value_inv(&self, init: &Self) -> bool {
//         &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
//         &&& map_iter(*self).initial_value_inv(&map_iter(*init))
//     }
//
//     uninterp spec fn decrease(&self) -> Option<nat>;
//
//     open spec fn peek(&self, index: int) -> Option<Self::Item> {
//         None
//         // REVIEW: It would be nice to use a definition like the one below,
//         //         but we don't have an output value to supply for ???
//         //         We also can't reference `remaining` since its prophetic
//         //         and `peek` is not
//         // match map_iter(*self).peek(index) {
//         //     Some(v) => Some(map_fun(*self).call_ensures((v,), ???),
//         //     None => None,
//         // }
//     }
// }

// impl <B, I, F> DoubleEndedIteratorSpecImpl for MyMap<B, I, F>
//     where I: DoubleEndedIterator + IteratorSpec,
//           F: FnMut(I::Item) -> B,
// {

//     open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
//         None // REVIEW: See note above for `peek`
//     }
// }


// // Spec version of I::map
// pub uninterp spec fn into_map_spec<B, I, F>(i: I, f: F) -> MyMap<B, I, F>
//     where
//         I: Iterator + IteratorSpec,
//         F: FnMut(I::Item) -> B,
// ;

// // Workaround issues with Verus support for default trait methods
// #[verifier::external_body]
// #[verifier::when_used_as_spec(into_map_spec)]
// pub fn to_map<B, I, F>(i: I, f: F) -> (r: MyMap<B, I, F>)
//     where
//         I: Iterator + IteratorSpec,
//         F: FnMut(I::Item) -> B,
//     requires
//         i.obeys_prophetic_iter_laws(),
//         forall |k| #![auto] 0 <= k < IteratorSpec::remaining(&i).len() ==> call_requires(f, (IteratorSpec::remaining(&i)[k], )),
//         i.initial_value_inv(&i),
//     ensures
//         r == into_map_spec::<B, I, F>(i, f),
//         IteratorSpec::remaining(&r).len() <= IteratorSpec::remaining(&i).len(),
//         forall |k| #![auto] 0 <= k < IteratorSpec::remaining(&r).len() ==> call_ensures(f, (IteratorSpec::remaining(&i)[k],), IteratorSpec::remaining(&r)[k]),
//         IteratorSpec::completes(&r) ==> IteratorSpec::completes(&i) &&
//             IteratorSpec::remaining(&r).len() == IteratorSpec::remaining(&i).len(),
//         IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&i) is Some,
//         IteratorSpec::initial_value_inv(&r, &r),
//         map_iter(r) == i,
//         map_fun(r) == f,
// {
//     todo!()
// }

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

    /// These properties help maintain the properties in wf,
    /// but they don't need to be exposed to the client
    #[verifier::prophetic]
    pub closed spec fn wf_inner(self) -> bool {
        &&& self.iter.remaining().len() == self.seq().len() - self.index@
        &&& forall |i| 0 <= i < self.iter.remaining().len() ==> #[trigger] self.iter.remaining()[i] == self.seq()[self.index@ + i]
        &&& self.iter.completes() ==> self.snapshot@.completes()
    }

    /// These properties are needed for the client code to verify
    #[verifier::prophetic]
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.index@ <= self.seq().len()
        &&& self.init@ matches Some(init) ==> self.snapshot@.initial_value_inv(init)
        &&& self.wf_inner()
        &&& self.iter.obeys_prophetic_iter_laws() ==> {
                &&& self.history@.len() == self.index@
                &&& forall |i| 0 <= i < self.index@ ==> #[trigger] self.history@[i] == self.seq()[i]
            }
    }

    /// Bundle the real iterator with its ghost state and loop invariants
    pub fn new(iter: I, init: Ghost<Option<&'a I>>) -> (s: Self)
        requires
            init@ matches Some(i) ==> iter.initial_value_inv(i),
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
            self.seq() == old(self).seq(),
            self.index@ == old(self).index@ + if ret is Some { 1int } else { 0 },
            self.snapshot == old(self).snapshot,
            self.init == old(self).init,
            self.iter.obeys_prophetic_iter_laws() ==> self.wf(),
            self.iter.obeys_prophetic_iter_laws() && ret is None ==>
                self.snapshot@.completes() && self.index@ == self.seq().len(),
            self.iter.obeys_prophetic_iter_laws() ==> (ret matches Some(r) ==>
                r == old(self).seq()[old(self).index@]),
            // History updates always hold
            ret matches Some(i) ==> self.history@ == old(self).history@.push(i),
            ret is None ==> self.history@ == old(self).history@,
            // TODO: Uncomment this line to replace everything below, once general mutable refs are supported
            // call_ensures(I::next, (&mut old(self).iter,), ret),
            self.iter.obeys_prophetic_iter_laws() == old(self).iter.obeys_prophetic_iter_laws(),
            self.iter.obeys_prophetic_iter_laws() ==> self.iter.completes() == old(self).iter.completes(),
            self.iter.obeys_prophetic_iter_laws() ==> (old(self).iter.decrease() is Some <==> self.iter.decrease() is Some),
            self.iter.obeys_prophetic_iter_laws() ==>
            ({
                if old(self).iter.remaining().len() > 0 {
                    &&& self.iter.remaining() == old(self).iter.remaining().drop_first()
                    &&& ret == Some(old(self).iter.remaining()[0])
                } else {
                    self.iter.remaining() === old(self).iter.remaining() && ret === None && self.iter.completes()
                }
            }),
            self.iter.obeys_prophetic_iter_laws() && old(self).iter.remaining().len() > 0 && self.iter.decrease() is Some ==>
                decreases_to!(old(self).iter.decrease()->0 => self.iter.decrease()->0),
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

// REVIEW: Can we automatically pull these in?
pub broadcast group group_iter_axioms {
    rev_postcondition,
    filter_postcondition,
    axiom_from_iterator_ensures,
}

} // verus!
