use super::super::prelude::*;
use super::super::seq::{
    group_seq_lemmas, lemma_seq_empty, lemma_seq_subrange_index, lemma_seq_subrange_len,
};
use core::iter::{Filter, FromIterator, Iterator, Rev, Skip, Take, Zip};

// Reduce the boilerplate in the definitions below.  We have to use a macro,
// since inside of ExIterator, we don't yet know that `self` is an Iterator.
// We use two macros so that we can convert arguments to Rust-friendly terms
// (e.g., by translating `final(.)` in to `verus_builtin::final_(.)` in `iter_state_preserved`
// before doing the real work in `iter_state_preserved_internal`
#[doc(hidden)]
#[macro_export]
macro_rules! iter_state_preserved_internal {
    ($before:expr, $after:expr $(,)?) => {
        // Dereference explicitly so method resolution uses the underlying
        // iterator, and `final` is consumed through a dereference.
        $crate::vstd::prelude::verus_proof_expr! {{
            &&& (*($after)).obeys_prophetic_iter_laws() == (*($before)).obeys_prophetic_iter_laws()
            &&& (*($before)).obeys_prophetic_iter_laws() ==>
                (*($before)).produces().len() == (*($before)).remaining().len()
            &&& (*($before)).obeys_prophetic_iter_laws() ==>
                ((*($after)).decrease() is Some <==> (*($before)).decrease() is Some)
        }}
    };
}

#[macro_export]
macro_rules! iter_state_preserved {
    ($($args:tt)*) => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::std_specs::iter::iter_state_preserved_internal!($($args)*))
    };
}

#[doc(hidden)]
pub use iter_state_preserved;
#[doc(hidden)]
pub use iter_state_preserved_internal;

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(IteratorSpec via IteratorSpecImpl)]
pub trait ExIterator {
    type ExternalTraitSpecificationFor: Iterator;

    type Item;

    /// This iterator obeys the specifications below on `next`,
    /// expressed in terms of prophetic spec functions.
    /// Only finite iterators (i.e., those that eventually return None
    /// and then continue to return None) or infinite iterators that
    /// never return None should use this interface.
    spec fn obeys_prophetic_iter_laws(&self) -> bool;

    /// Sequence of all potentially returned items
    #[verifier::prophetic]
    spec fn remaining(&self) -> Seq<Self::Item>;

    /// For each potential item in `remaining()`, does the item actually
    /// get returned, or does the iterator get "stuck" trying to produce it,
    /// e.g., because a client supplied a closure that diverges?
    #[verifier::prophetic]
    spec fn produces(&self) -> Seq<bool>;

    /// Advances the iterator and returns the next value.
    fn next(&mut self) -> (ret: Option<Self::Item>)
        ensures
            iter_state_preserved!(old(self), final(self)),
            // `next` pops the head of the prophesized remaining(), or returns None
            final(self).obeys_prophetic_iter_laws() ==>
            ({
                if old(self).remaining().len() > 0 {
                    &&& final(self).remaining() == old(self).remaining().drop_first()
                    &&& final(self).produces() == old(self).produces().drop_first()
                    &&& ret == Some(old(self).remaining()[0])
                    &&& old(self).produces()[0]
                } else {
                    &&& final(self).remaining() == old(self).remaining()
                    &&& final(self).produces() == old(self).produces()
                    &&& ret == None
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

    // If we can make a useful guess as to what the i-th value will be, return it.
    // Otherwise, return None.
    spec fn peek(&self, index: int) -> Option<Self::Item>;



    /******* Provided methods (in alphabetical order) *********/
    // For provided method that returns a new iterator (e.g., filter, map, or zip),
    // ideally we would write their postconditions here.  However, this requires
    // a trait bound of `Self: IteratorSpec`, which introduces a cyclic dependency.
    // Hence, we introduce a layer of indirection via an uninterp spec function that
    // describes the postconditions.

    // TODO: The Rust implementations of `all`, `any`, `find`, `find_map` and `position` depend on a correct implementation of `try_fold`
    //       For now, we assume obeys_prophetic_iter_laws() entails such an implementation, but we should
    //       eventually constrain implementations of `try_fold` to actually be correct enough to uphold the specs below.

    fn all<F>(&mut self, f: F) -> (r: bool)
        where Self: Sized,
            F: FnMut(Self::Item) -> bool
        requires
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> f.requires((#[trigger] self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `f` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: Self::Item| #[trigger] f.requires((x, )),
        ensures
            iter_state_preserved!(old(self), final(self)),
            final(self).obeys_prophetic_iter_laws() ==> {
                let num_consumed = old(self).remaining().len() - final(self).remaining().len();
                &&& final(self).remaining().is_suffix_of(old(self).remaining())
                &&& final(self).produces() == old(self).produces().skip(num_consumed)
                &&& old(self).produces().take(num_consumed).all(|p: bool| p)
            },
            // If all returns true, then the iterator has no remaining elements,
            // and the predicate was true for all of the original iterator's elements.
            final(self).obeys_prophetic_iter_laws() && r ==> {
                &&& final(self).remaining().len() == 0
                &&& forall |i| 0 <= i < old(self).remaining().len() ==>
                    f.ensures((#[trigger] old(self).remaining()[i],), true)
            },
            // If all returns false, then there is some element for which the
            // predicate was false, and all previous elements satisfied the predicate.
            final(self).obeys_prophetic_iter_laws() && !r ==> {
                let idx = old(self).remaining().len() - final(self).remaining().len() - 1;
                {
                    // The failing element was consumed, so the remaining sequence strictly shrank
                    &&& final(self).remaining().len() < old(self).remaining().len()
                    &&& f.ensures((old(self).remaining()[idx],), false)
                    &&& forall |i| 0 <= i < idx ==>
                        f.ensures((#[trigger] old(self).remaining()[i],), true)
                }
            };

    fn any<F>(&mut self, f: F) -> (r: bool)
        where Self: Sized,
            F: FnMut(Self::Item) -> bool
        requires
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> f.requires((#[trigger] self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `f` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: Self::Item| #[trigger] f.requires((x, )),
        ensures
            iter_state_preserved!(old(self), final(self)),
            final(self).obeys_prophetic_iter_laws() ==> {
                let num_consumed = old(self).remaining().len() - final(self).remaining().len();
                &&& final(self).remaining().is_suffix_of(old(self).remaining())
                &&& final(self).produces() == old(self).produces().skip(num_consumed)
                &&& old(self).produces().take(num_consumed).all(|p: bool| p)
            },
            // If any returns false, then the iterator has no remaining elements,
            // and the predicate was false for all of the original iterator's elements.
            final(self).obeys_prophetic_iter_laws() && !r ==> {
                &&& final(self).remaining().len() == 0
                &&& forall |i| 0 <= i < old(self).remaining().len() ==>
                    f.ensures((#[trigger] old(self).remaining()[i],), false)
            },
            // If any returns true, then there is some element that satisfied the predicate,
            // and all previous elements did not satisfy the predicate.
            final(self).obeys_prophetic_iter_laws() && r ==> {
                let idx = old(self).remaining().len() - final(self).remaining().len() - 1;
                {
                    // The satisfying element was consumed, so the remaining sequence strictly shrank
                    &&& final(self).remaining().len() < old(self).remaining().len()
                    &&& f.ensures((old(self).remaining()[idx],), true)
                    &&& forall |i| 0 <= i < idx ==>
                        f.ensures((#[trigger] old(self).remaining()[i],), false)
                }
            };

    fn collect<B>(self) -> (collection: B)
        where
            B: FromIterator<Self::Item>,
            Self: Sized,
        ensures
            self.obeys_prophetic_iter_laws() ==>
                FromIteratorSpec::from_iter_ensures(self.remaining(), self.produces(), collection),
    ;

    fn filter<P>(self, predicate: P) -> (r: core::iter::Filter<Self, P>)
        where
            Self: Sized,
            P: FnMut(&Self::Item) -> bool,
        requires
            // `filter`'s implementation loops over the inner iterator until the predicate accepts an element,
            // so it needs a decreases metric to prove termination.
            self.decrease() is Some,
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> predicate.requires((#[trigger] &self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `predicate` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: &Self::Item| #[trigger] predicate.requires((x, )),
        ensures
            self.obeys_prophetic_iter_laws() ==> filter_post(self, predicate, r),
    ;

    fn find<P>(&mut self, predicate: P) -> (r: Option<Self::Item>)
        where Self: Sized,
            P: FnMut(&Self::Item) -> bool
        requires
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> predicate.requires((#[trigger] &self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `predicate` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: &Self::Item| #[trigger] predicate.requires((x, )),
        ensures
            iter_state_preserved!(old(self), final(self)),
            final(self).obeys_prophetic_iter_laws() ==> final(self).produces() ==
                old(self).produces().skip(old(self).remaining().len() - final(self).remaining().len()),
            final(self).obeys_prophetic_iter_laws() ==> {
                &&& final(self).remaining().is_suffix_of(old(self).remaining())
                &&& old(self).produces().take(old(self).remaining().len() - final(self).remaining().len()).all(|p: bool| p)
            },
            // If find returns None, then the iterator has no remaining
            // elements, and the predicate was false for all of the original
            // iterator's elements.
            final(self).obeys_prophetic_iter_laws() && r.is_none() ==> {
                &&& final(self).remaining().len() == 0
                &&& forall |i| 0 <= i < old(self).remaining().len() ==>
                    predicate.ensures((#[trigger]&old(self).remaining()[i],), false)
            },
            // If find returns Some, then the returned value satisfies the
            // predicate, and all previous elements did not satisfy the
            // predicate.
            final(self).obeys_prophetic_iter_laws() && r.is_some() ==> {
                let idx = old(self).remaining().len() - final(self).remaining().len() - 1;
                {
                    &&& 0 <= final(self).remaining().len() < old(self).remaining().len()
                    &&& predicate.ensures((&r.unwrap(),), true)
                    &&& old(self).remaining()[idx] == r.unwrap()
                    &&& forall |i| 0 <= i < idx ==>
                        predicate.ensures((#[trigger] &old(self).remaining()[i],), false)
                }
            };

    fn find_map<B, F>(&mut self, f: F) -> (r: Option<B>)
        where Self: Sized,
            F: FnMut(Self::Item) -> Option<B>
        requires
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> f.requires((#[trigger] self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `f` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: Self::Item| #[trigger] f.requires((x, )),
        ensures
            iter_state_preserved!(old(self), final(self)),

            final(self).obeys_prophetic_iter_laws() ==> {
                let num_consumed = old(self).remaining().len() - final(self).remaining().len();
                &&& final(self).remaining().is_suffix_of(old(self).remaining())
                &&& final(self).produces() == old(self).produces().skip(num_consumed)
                &&& old(self).produces().take(num_consumed).all(|p: bool| p)
            },
            // If find_map returns None, then the iterator has no remaining
            // elements, and f was None for all of the original
            // iterator's elements.
            final(self).obeys_prophetic_iter_laws() && r.is_none() ==> {
                &&& final(self).remaining().len() == 0
                &&& forall |i| 0 <= i < old(self).remaining().len() ==>
                    f.ensures((#[trigger]old(self).remaining()[i],), None)
            },
            // If find_map returns Some, then the returned value satisfies f,
            // and all previous elements did not satisfy f
            final(self).obeys_prophetic_iter_laws() && r.is_some() ==> {
                let idx = old(self).remaining().len() - final(self).remaining().len() - 1;
                {
                    &&& 0 <= final(self).remaining().len() < old(self).remaining().len()
                    &&& f.ensures((old(self).remaining()[idx],), r)
                    &&& forall |i| 0 <= i < idx ==>
                        f.ensures((#[trigger] old(self).remaining()[i],), None)
                }
            };

    fn map<B, F>(self, f: F) -> (r: core::iter::Map<Self, F>)
        where
            Self: Sized,
            F: FnMut(Self::Item) -> B,
        requires
            self.obeys_prophetic_iter_laws() ==> forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> f.requires((#[trigger] self.remaining()[k], )),
            // without the laws, `remaining()` says nothing about the items `f` is called on
            !self.obeys_prophetic_iter_laws() ==> forall |x: Self::Item| #[trigger] f.requires((x, )),
        ensures
            self.obeys_prophetic_iter_laws() ==> map_post(self, f, r),
    ;

    fn position<P>(&mut self, predicate: P) -> (r: Option<usize>)
        where
            Self: Sized,
            P: FnMut(Self::Item) -> bool,
        requires
            // without the laws, `remaining()` bounds neither the count std's `position` keeps
            // (which may overflow) nor the items `predicate` is called on
            self.obeys_prophetic_iter_laws(),
            self.remaining().len() <= usize::MAX as int,
            forall |k| 0 <= k < self.remaining().len() && self.produces()[k] ==> predicate.requires((#[trigger] self.remaining()[k], )),
        ensures
            iter_state_preserved!(old(self), final(self)),
            final(self).obeys_prophetic_iter_laws() ==> {
                let num_consumed = old(self).remaining().len() - final(self).remaining().len();
                &&& final(self).remaining().is_suffix_of(old(self).remaining())
                &&& final(self).produces() == old(self).produces().skip(num_consumed)
                &&& old(self).produces().take(num_consumed).all(|p: bool| p)
            },
            // If position returns None, then the iterator has no remaining
            // elements, and the predicate was false for all of the original
            // iterator's elements.
            final(self).obeys_prophetic_iter_laws() && r.is_none() ==> {
                &&& final(self).remaining().len() == 0
                &&& forall |i| 0 <= i < old(self).remaining().len() ==>
                    predicate.ensures((#[trigger] old(self).remaining()[i],), false)
            },
            // If position returns Some, then the returned index whose value satisfies the
            // predicate, and all previous elements did not satisfy the predicate.
            final(self).obeys_prophetic_iter_laws() && r.is_some() ==> {
                let index = r.unwrap();
                {
                    &&& index as int == (old(self).remaining().len() - final(self).remaining().len() - 1)
                    &&& 0 <= final(self).remaining().len() < old(self).remaining().len()
                    &&& predicate.ensures((#[trigger] old(self).remaining()[index as int],), true)
                    &&& forall |i| 0 <= i < index as int ==>
                        predicate.ensures((#[trigger] old(self).remaining()[i],), false)
                }
            };

    fn rev(self) -> (r: Rev<Self>)
        where Self: Sized,
        ensures
            self.obeys_prophetic_iter_laws() ==> rev_post(self, r),
    ;

    fn size_hint(&self) -> ((lower, upper): (usize, Option<usize>))
        ensures
            self.obeys_prophetic_iter_laws() ==>
                lower <= self.remaining().len() && (upper matches Some(b) ==> self.remaining().len() <= b),
        default_ensures
            (lower, upper) == (0usize, None),
    ;

    fn skip(self, n: usize) -> (s: Skip<Self>)
        where Self: Sized,
        ensures
            self.obeys_prophetic_iter_laws() ==> skip_post(self, n, s),
    ;

    fn take(self, n: usize) -> (t: Take<Self>)
        where Self: Sized,
        ensures
            self.obeys_prophetic_iter_laws() ==> take_post(self, n, t),
    ;

    #[verifier::impls_cannot_extend_spec]
    fn zip<U>(self, other: U) -> (r: Zip<Self, <U as IntoIterator>::IntoIter>)
        where
            Self: Sized,
            U: IntoIterator,
        ensures
            self.obeys_prophetic_iter_laws() ==> zip_post(self, other, r),
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
            iter_state_preserved!(old(self), final(self)),
            // `next_back` pops the tail of the prophesized remaining(), or returns None
            <Self as IteratorSpec>::obeys_prophetic_iter_laws(final(self)) ==>
            ({
                if <Self as IteratorSpec>::remaining(old(self)).len() > 0 {
                    &&& <Self as IteratorSpec>::remaining(final(self)) == <Self as IteratorSpec>::remaining(old(self)).drop_last()
                    &&& <Self as IteratorSpec>::produces(final(self)) == <Self as IteratorSpec>::produces(old(self)).drop_last()
                    &&& ret == Some(<Self as IteratorSpec>::remaining(old(self)).last())
                    &&& <Self as IteratorSpec>::produces(old(self)).last()
                } else {
                    &&& <Self as IteratorSpec>::remaining(final(self)) == <Self as IteratorSpec>::remaining(old(self))
                    &&& <Self as IteratorSpec>::produces(final(self)) == <Self as IteratorSpec>::produces(old(self))
                    &&& ret == None
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

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(ExactSizeIteratorSpec via ExactSizeIteratorSpecImpl)]
pub trait ExExactSizeIterator: Iterator {
    type ExternalTraitSpecificationFor: ExactSizeIterator;

    // An `ExactSizeIterator` can specify its length non-prophetically,
    // i.e., without using `self.remaining().len()`.
    spec fn exact_len(&self) -> usize;

    fn len(&self) -> (len: usize)
        ensures
            self.obeys_prophetic_iter_laws() ==> len == self.exact_len() == self.remaining().len() == self.produces().len(),
    ;
}

/********************************************************************************
 * Definitions for `IntoIterator` and `FromIterator``
 ********************************************************************************/
#[verifier::external_trait_specification]
pub trait ExIntoIterator {
    type ExternalTraitSpecificationFor: core::iter::IntoIterator;

    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter;
}

pub open spec fn iter_into_iter_spec<I: Iterator>(i: I) -> I {
    i
}

#[verifier::when_used_as_spec(iter_into_iter_spec)]
pub assume_specification<I: Iterator>[ <I as IntoIterator>::into_iter ](i: I) -> (r: I)
    ensures
        r == i,
;

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FromIteratorSpec via FromIteratorSpecImpl)]
pub trait ExFromIterator<A>: Sized {
    type ExternalTraitSpecificationFor: FromIterator<A>;

    // `produces` indicates whether the items at indices in `remaining` are actually computed
    spec fn from_iter_ensures(remaining: Seq<A>, produces: Seq<bool>, s: Self) -> bool;

    // from_iter may be nondeterministic, which we represent with an existential
    #[verifier::impls_cannot_extend_spec]
    fn from_iter<T>(iter: T) -> (s: Self)
       where T: IntoIterator<Item = A>
        ensures
            exists |initial: T::IntoIter|
                #[trigger] (T::into_iter).ensures((iter,), initial)
                && (initial.obeys_prophetic_iter_laws() ==>
                    Self::from_iter_ensures(initial.remaining(), initial.produces(), s)),
    ;
}

/********************************************************************************
 * Definitions for `&mut I`
 ********************************************************************************/
// Forwarding spec impl for the Rust-supplied blanket `impl<I> Iterator for &mut I`.
// Without this, bare method-call syntax on a `i: &mut I` receiver (e.g. `i.remaining()`)
// resolves to these (otherwise uninterpreted) functions on `&mut I` rather than on `I`,
// silently disconnecting clients from `I`'s actual specs.
impl <I> IteratorSpecImpl for &mut I
    where I: Iterator {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        <I as IteratorSpec>::obeys_prophetic_iter_laws(*self)
    }

    #[verifier::prophetic]
    open spec fn remaining(&self) -> Seq<Self::Item> {
        <I as IteratorSpec>::remaining(*self)
    }

    #[verifier::prophetic]
    open spec fn produces(&self) -> Seq<bool> {
        <I as IteratorSpec>::produces(*self)
    }

    open spec fn decrease(&self) -> Option<nat> {
        <I as IteratorSpec>::decrease(*self)
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        <I as IteratorSpec>::peek(*self, index)
    }
}

/********************************************************************************
 * Definitions for `filter()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(F)]
pub struct ExFilter<I, F>(Filter<I, F>);

// Ghost accessor for the inner iterator
pub uninterp spec fn filter_iter<I, F>(r: Filter<I, F>) -> I;

// Ghost accessor for the inner predicate
pub uninterp spec fn filter_fun<I, F>(r: Filter<I, F>) -> F;

// Ghost accessor for the decisions at every inner position.
#[verifier::prophetic]
pub uninterp spec fn filter_keep<I, F>(r: Filter<I, F>) -> Seq<bool>;

// Define Iter::filter's postcondition
pub uninterp spec fn filter_post<I, F>(i: I, f: F, r: Filter<I, F>) -> bool;

// See examples/iterators/map_and_filter.rs for a verified version of this interface.
// Any changes here should first be verified over there.
pub broadcast axiom fn filter_postcondition<I, F>(i: I, f: F, r: core::iter::Filter<I, F>)
    where
        I: IteratorSpec,
        F: FnMut(&I::Item) -> bool,
    requires
        #[trigger] filter_post(i, f, r),
    ensures
        {
            let keep = filter_keep(r);
            {
            // Discarding a position requires producing its value and a false predicate result.
            // A position that gets stuck is retained, with a false production flag.
            &&& keep.len() == i.remaining().len()
            &&& forall |j| 0 <= j < keep.len() && !(#[trigger] keep[j]) ==>
                i.produces()[j] && f.ensures((&i.remaining()[j],), false)
            &&& forall |j| 0 <= j < keep.len() && #[trigger] keep[j] ==> {
                let k = i.remaining()[..j].filter_index(|idx: int| keep[idx]).len() as int;
                IteratorSpec::produces(&r)[k] ==>
                    i.produces()[j] && f.ensures((&i.remaining()[j],), true)
            }
            // Completeness: Every inner element the predicate keeps is retained and in order.
            &&& IteratorSpec::remaining(&r) == i.remaining().filter_index(|j: int| keep[j])
            // Expose the size bound and source positions directly for convenience.
            &&& IteratorSpec::produces(&r).len() == IteratorSpec::remaining(&r).len()
            &&& IteratorSpec::remaining(&r).len() <= i.remaining().len()
            &&& forall |k| #![trigger IteratorSpec::remaining(&r)[k]] 0 <= k < IteratorSpec::remaining(&r).len() ==>
                    exists |j| 0 <= j < i.remaining().len()
                        && IteratorSpec::remaining(&r)[k] == #[trigger] i.remaining()[j]
                        && keep[j]
                        && k == i.remaining()[..j].filter_index(|idx: int| keep[idx]).len()
                        && (IteratorSpec::produces(&r)[k] ==>
                            i.produces()[j] && f.ensures((&i.remaining()[j],), true))
            &&& IteratorSpec::decrease(&r) is Some == i.decrease() is Some
            &&& filter_iter(r) == i
            &&& filter_fun(r) == f
            }
        },
;

impl <I, P> IteratorSpecImpl for core::iter::Filter<I, P>
    where
        I: Iterator + IteratorSpec,
        P: FnMut(&I::Item) -> bool,
{
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        filter_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    uninterp spec fn produces(&self) -> Seq<bool>;

    uninterp spec fn decrease(&self) -> Option<nat>;

    // `filter` cannot make a useful static guess about which element will be returned at a given index,
    // since that depends on prophetic evaluations of the predicate.
    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
    }
}

/********************************************************************************
 * Definitions for `map()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(F)]
pub struct ExMap<I, F>(core::iter::Map<I, F>);

// Ghost accessor for the inner iterator
pub uninterp spec fn map_iter<I, F>(r: core::iter::Map<I, F>) -> I;

// Ghost accessor for the inner function
pub uninterp spec fn map_fun<I, F>(r: core::iter::Map<I, F>) -> F;

// Define Iter::map's postcondition
pub uninterp spec fn map_post<I, F>(i: I, f: F, r: core::iter::Map<I, F>) -> bool;

// See examples/iterators/map_and_filter.rs for a verified version of this interface.
// Any changes here should first be verified over there.
pub broadcast axiom fn map_postcondition<I, F>(i: I, f: F, r: core::iter::Map<I, F>)
    where
        I: IteratorSpec,
        F: FnMut<(I::Item,)>,
    requires
        #[trigger] map_post(i, f, r),
    ensures
        IteratorSpec::remaining(&r).len() == i.remaining().len(),
        IteratorSpec::produces(&r).len() == IteratorSpec::remaining(&r).len(),
        forall |k| #![trigger IteratorSpec::remaining(&r)[k]] #![trigger IteratorSpec::produces(&r)[k]]
            0 <= k < IteratorSpec::remaining(&r).len() && IteratorSpec::produces(&r)[k] ==>
            i.produces()[k] && f.ensures((i.remaining()[k],), IteratorSpec::remaining(&r)[k]),
        IteratorSpec::decrease(&r) is Some == i.decrease() is Some,
        map_iter(r) == i,
        map_fun(r) == f,
;

impl <B, I, F> IteratorSpecImpl for core::iter::Map<I, F>
    where
        I: Iterator + IteratorSpec,
        F: FnMut(I::Item) -> B,
{

    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        map_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<B>;

    #[verifier::prophetic]
    uninterp spec fn produces(&self) -> Seq<bool>;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<B> {
        match map_iter(*self).peek(index) {
            Some(v) => {
                let x = choose |x| map_fun(*self).ensures((v,), x);
                Some(x)
            }
            None => None,
        }
    }
}

impl <B, I, F> DoubleEndedIteratorSpecImpl for core::iter::Map<I, F>
    where I: DoubleEndedIterator + IteratorSpec,
          F: FnMut(I::Item) -> B,
{
    open spec fn peek_back(&self, index: int) -> Option<B> {
        match map_iter(*self).peek_back(index) {
            Some(v) => {
                let x = choose |x| map_fun(*self).ensures((v,), x);
                Some(x)
            }
            None => None,
        }
    }
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

// Define Iter::rev's postcondition
pub uninterp spec fn rev_post<I>(i: I, r: Rev<I>) -> bool;

pub broadcast axiom fn rev_postcondition<I: DoubleEndedIteratorSpec>(i: I, r: Rev<I>)
    requires
        #[trigger] rev_post(i, r),
    ensures
        IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse(),
        IteratorSpec::produces(&r) == i.produces().reverse(),
        IteratorSpec::decrease(&r) is Some == i.decrease() is Some,
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
    closed spec fn produces(&self) -> Seq<bool> {
        rev_iter(*self).produces().reverse()
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
 * Definitions for `skip()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
pub struct ExSkip<I>(Skip<I>);

// Ghost accessor for the inner iterator
pub uninterp spec fn skip_iter<I>(s: Skip<I>) -> I;

// Ghost accessor for the initial count of items to skip
pub uninterp spec fn skip_init_n<I>(s: Skip<I>) -> usize;

// Define Iter::skip's postcondition
pub uninterp spec fn skip_post<I>(i: I, n: usize, s: Skip<I>) -> bool;

pub broadcast axiom fn skip_postcondition<I: IteratorSpec>(i: I, n: usize, r: Skip<I>)
    requires
        i.obeys_prophetic_iter_laws(),
        #[trigger] skip_post(i, n, r),
    ensures
        IteratorSpec::remaining(&r) == if i.remaining().len() < n { Seq::empty() } else { i.remaining()[n..] },
        IteratorSpec::produces(&r) == if i.remaining().len() < n { Seq::empty() } else { i.produces()[n..] },
        skip_iter(r) == i,
        skip_init_n(r) == n,
        IteratorSpec::decrease(&r) is Some == i.decrease() is Some,
;

impl <I> IteratorSpecImpl for Skip<I>
    where I: Iterator {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        skip_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    uninterp spec fn produces(&self) -> Seq<bool>;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        skip_iter(*self).peek(skip_init_n(*self) + index)
    }
}

impl <I> DoubleEndedIteratorSpecImpl for Skip<I>
    where I: DoubleEndedIteratorSpec + ExactSizeIteratorSpec
{
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        // Skip only drops elements from the front, so the back of the skipped
        // sequence coincides with the back of the inner iterator, as long as
        // `index` stays within the (un-skipped) remaining elements.
        let len = skip_iter(*self).exact_len();
        if len < skip_init_n(*self) || index >= len - skip_init_n(*self) {
            None
        } else {
            skip_iter(*self).peek_back(index)
        }
    }
}

/********************************************************************************
 * Definitions for `take()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
pub struct ExTake<I>(Take<I>);

// Ghost accessor for the inner iterator
pub uninterp spec fn take_iter<I>(r: Take<I>) -> I;

// Ghost accessor for the count
pub uninterp spec fn take_count<I>(r: Take<I>) -> usize;

// Define Iter::take's postcondition
pub uninterp spec fn take_post<I>(i: I, n: usize, t: Take<I>) -> bool;

// See examples/iterators/take.rs for a verified version of this interface.
// Any changes here should first be verified over there.
pub broadcast axiom fn take_postcondition<I: IteratorSpec>(i: I, n: usize, r: Take<I>)
    requires
        i.obeys_prophetic_iter_laws(),
        #[trigger] take_post(i, n, r),
    ensures
        IteratorSpec::remaining(&r) == if i.remaining().len() < n { i.remaining() } else { i.remaining()[..n] },
        IteratorSpec::produces(&r) == if i.remaining().len() < n { i.produces() } else { i.produces()[..n] },
        take_iter(r) == i,
        take_count(r) == n,
        IteratorSpec::decrease(&r) is Some,
;

impl <I> IteratorSpecImpl for Take<I>
    where I: Iterator {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        take_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<Self::Item>;

    #[verifier::prophetic]
    uninterp spec fn produces(&self) -> Seq<bool>;

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        take_iter(*self).peek(index)
    }
}

impl <I> DoubleEndedIteratorSpecImpl for Take<I>
    where I: DoubleEndedIteratorSpec + ExactSizeIteratorSpec
{
    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        let len = take_iter(*self).exact_len();
        if len < take_count(*self) {
            None
        } else {
            take_iter(*self).peek_back(len - take_count(*self) - index - 1)
        }
    }
}

/********************************************************************************
 * Definitions for `zip()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(B)]
pub struct ExZip<A, B>(Zip<A, B>);

// Ghost accessor for the first inner iterator
pub uninterp spec fn zip_iter_fst<A, B>(z: Zip<A, B>) -> A;

// Ghost accessor for the second inner iterator
pub uninterp spec fn zip_iter_snd<A, B>(z: Zip<A, B>) -> B;

impl<A, B> IteratorSpecImpl for Zip<A, B>
    where A: Iterator + IteratorSpec, B: Iterator + IteratorSpec
{
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        &&& zip_iter_fst(*self).obeys_prophetic_iter_laws()
        &&& zip_iter_snd(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    closed spec fn remaining(&self) -> Seq<Self::Item> {
        zip_iter_fst(*self).remaining().zip_truncate(zip_iter_snd(*self).remaining())
    }

    #[verifier::prophetic]
    closed spec fn produces(&self) -> Seq<bool> {
        zip_iter_fst(*self).produces().zip_truncate(zip_iter_snd(*self).produces()).map_values(|p: (bool, bool)| p.0 && p.1)
    }

    closed spec fn decrease(&self) -> Option<nat> {
        match (zip_iter_fst(*self).decrease(), zip_iter_snd(*self).decrease()) {
            (Some(a), Some(b)) => if a <= b { Some(a) } else { Some(b) },
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        match (zip_iter_fst(*self).peek(index), zip_iter_snd(*self).peek(index)) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }
}

// Define Iter::zip's postcondition
pub uninterp spec fn zip_post<I, U, Z>(i: I, other: U, r: Z) -> bool;

pub broadcast axiom fn zip_postcondition<I, U>(i: I, other: U, r: Zip<I, <U as IntoIterator>::IntoIter>)
    where
            I: Sized + IteratorSpec,
            U: IntoIterator, //Spec,
    requires
        i.obeys_prophetic_iter_laws(),
        #[trigger] zip_post(i, other, r),
    ensures
        (U::into_iter).ensures((other,), zip_iter_snd(r)),
        zip_iter_fst(r) == i,
        IteratorSpec::remaining(&r) == i.remaining().zip_truncate(zip_iter_snd(r).remaining()),
        IteratorSpec::produces(&r) == i.produces().zip_truncate(zip_iter_snd(r).produces()).map_values(|p: (bool, bool)| p.0 && p.1),
        IteratorSpec::decrease(&r) is Some == (i.decrease() is Some || zip_iter_snd(r).decrease() is Some),
;

/********************************************************************************
 * Defines a convenient wrapper type that bundles state and invariants needed
 * for ergonomic for-loop support.
 ********************************************************************************/

pub struct VerusForLoopWrapper<I: Iterator> {
    pub index: Ghost<int>,
    pub snapshot: Ghost<I>,
    pub iter: I,
    pub history: Ghost<Seq<I::Item>>,
}

impl <I: Iterator> VerusForLoopWrapper<I> {
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
        &&& self.index() <= self.snapshot@.produces().len()
        &&& self.iter.produces() == self.snapshot@.produces().skip(self.index())
    }

    /// These properties are needed for the client code to verify
    #[verifier::prophetic]
    pub open spec fn wf(self) -> bool {
        &&& 0 <= self.index() <= self.seq().len()
        &&& self.wf_inner()
        &&& self.iter.obeys_prophetic_iter_laws() ==> {
                &&& self.history@.len() == self.index()
                &&& forall |i| 0 <= i < self.index() ==> #[trigger] self.history@[i] == self.seq()[i]
                &&& self.snapshot@.produces().take(self.index()).all(|p: bool| p)
            }
    }

    /// Bundle the real iterator with its ghost state and loop invariants
    pub fn new(iter: I) -> (s: Self)
        ensures
            s.index == 0,
            s.snapshot == iter,
            s.iter == iter,
            s.history@ == Seq::<I::Item>::empty(),
            s.wf(),
    {
        broadcast use group_seq_lemmas;
        proof {
            assert(iter.produces().skip(0) =~= iter.produces());
        }
        VerusForLoopWrapper {
            index: Ghost(0),
            snapshot: Ghost(iter),
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
            final(self).iter.obeys_prophetic_iter_laws() ==> final(self).wf(),
            final(self).iter.obeys_prophetic_iter_laws() && ret is None ==>
                final(self).index() == final(self).seq().len()
                    && final(self).snapshot@.produces().all(|p: bool| p),
            final(self).iter.obeys_prophetic_iter_laws() ==> (ret matches Some(r) ==>
                r == old(self).seq()[old(self).index()] && old(self).snapshot@.produces()[old(self).index()]),
            // History updates always hold
            ret matches Some(i) ==> final(self).history@ == old(self).history@.push(i),
            ret is None ==> final(self).history@ == old(self).history@,
            // All of the standard Iterator::next guarantees still hold
            exists |m: &mut I| #![auto] (I::next).ensures((m,), ret) && *m == old(self).iter && *final(m) == final(self).iter,
    {
        let ghost old_history = self.history@;
        let ret = self.iter.next();
        if ret.is_some() {
            self.history = Ghost(old_history.push(ret->0));
        }
        proof {
            broadcast use group_seq_lemmas;
            if ret.is_some() {
                self.index@ = self.index@ + 1;
            }
            if self.iter.obeys_prophetic_iter_laws() {
                assert(self.snapshot@.produces().len() == self.seq().len());
                assert(self.iter.produces() =~= self.snapshot@.produces().skip(self.index()));
                if ret.is_none() {
                    assert(self.snapshot@.produces().take(self.index()) =~= self.snapshot@.produces());
                }
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
    zip_postcondition,
    filter_postcondition,
    take_postcondition,
    skip_postcondition,
    map_postcondition,
}

} // verus!
