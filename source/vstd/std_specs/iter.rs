use super::super::prelude::*;
use super::super::seq::{axiom_seq_subrange_index, axiom_seq_subrange_len, axiom_seq_empty, group_seq_axioms};

use verus as verus_;

use core::iter::{Iterator,Rev};

verus_! {

#[verifier::external_trait_specification]
pub trait ExIntoIterator {
    type ExternalTraitSpecificationFor: core::iter::IntoIterator;
}

#[verifier::external_trait_specification]
pub trait ExIterStep: Clone + PartialOrd + Sized {
    type ExternalTraitSpecificationFor: core::iter::Step;
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

    
    // #[verifier::when_used_as_spec(into_rev_spec)]
    // FAILS with: error: found a cyclic self-reference in a definition, which may result in nontermination
    // fn rev(self) -> (r: Rev<Self>)
    //     where Self: Sized + DoubleEndedIterator, // + DoubleEndedIteratorSpec,
    //     // requires
    //     //     self.obeys_prophetic_iter_laws(),   // REVIEW: Should this be moved to an implication on the ensures clauses?
    //     //     self.initial_value_inv(&self),
    //     default_ensures
    //         r == into_rev_spec(self),
    //         // r.remaining(&r) == self.remaining().reverse(),
    //         // r.completes(&r) == self.completes(),
    //         // r.decrease(&r) is Some == self.decrease() is Some,
    //         // r.initial_value_inv(&r),
    // ;

    // FAILS with: error[E0034]: multiple applicable items in scope
    //
    // #[verifier::when_used_as_spec(into_rev_spec)]
    // #[verifier::external_body]
    // fn rev(self) -> (r: Rev<Self>)
    //     where Self: Sized + DoubleEndedIterator, // + DoubleEndedIteratorSpec,
    //     requires
    //         self.obeys_prophetic_iter_laws(),   // REVIEW: Should this be moved to an implication on the ensures clauses?
    //         IteratorSpec::initial_value_inv(&self, &self),
    //     default_ensures
    //         r == into_rev_spec(self),
    //         IteratorSpec::remaining(&r) == IteratorSpec::remaining(&self).reverse(),
    //         IteratorSpec::completes(&r) == IteratorSpec::completes(&self),
    //         IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&self) is Some,
    //         IteratorSpec::initial_value_inv(&r, &r),
    // {
    //     //Rev::new(self)
    //     self.rev()
    // }
}

// FAILS with: error: assume_specification cannot be used to specify generic specifications of trait methods; consider using external_trait_specification instead
//  #[verifier::when_used_as_spec(into_rev_spec)]
//  pub assume_specification<I> [Iterator::rev](i: I) -> (r: Rev<I>)
//     where I: Sized + DoubleEndedIterator + DoubleEndedIteratorSpec,
//     requires
//         i.obeys_prophetic_iter_laws(),
//     default_ensures
//         r == into_rev_spec(i),
//         IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse(),
//         IteratorSpec::completes(&r) == IteratorSpec::completes(&i),
//         IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&i) is Some,
//         IteratorSpec::initial_value_inv(&r, &r),
//     ;

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
 * Definitions for `rev()`
 ********************************************************************************/
#[verifier::external_body]
#[verifier::external_type_specification]
#[verifier::reject_recursive_types(I)]
pub struct ExRev<I>(Rev<I>);

// Ghost accessor for the inner iterator
pub uninterp spec fn rev_iter<I>(r: Rev<I>) -> I;

// Spec version of Rev::new
pub uninterp spec fn into_rev_spec<I: DoubleEndedIterator + DoubleEndedIteratorSpec>(i: I) -> Rev<I>;

//  #[verifier::when_used_as_spec(into_rev_spec)]
//  assume_specification<I> [Rev::new](i: I) -> (r: Rev<I>)
//     where I: Sized + DoubleEndedIterator + DoubleEndedIteratorSpec,
//     requires
//         i.obeys_prophetic_iter_laws(),   // REVIEW: Should this be moved to an implication on the ensures clauses?
//         IteratorSpec::initial_value_inv(&self, &self),
//     ensures
//         r == into_rev_spec(i),
//         IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse(),
//         IteratorSpec::completes(&r) == IteratorSpec::completes(&i),
//         IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&i) is Some,
//         IteratorSpec::initial_value_inv(&r, &r),
//     ;



// // Workaround issues with Verus support for default trait methods
#[verifier::external_body]
#[verifier::when_used_as_spec(into_rev_spec)]
pub fn to_rev<I: DoubleEndedIterator + DoubleEndedIteratorSpec>(i: I) -> (r: Rev<I>)
    requires
        i.obeys_prophetic_iter_laws(),
        i.initial_value_inv(&i),
    ensures
        r == into_rev_spec(i),
        IteratorSpec::remaining(&r) == IteratorSpec::remaining(&i).reverse(),
        IteratorSpec::completes(&r) == IteratorSpec::completes(&i),
        IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&i) is Some,
        IteratorSpec::initial_value_inv(&r, &r),
{
    i.rev()
}

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
 * Definitions for `map()`
 ********************************************************************************/

// FAILS: error: the type parameter `A58_B` is not constrained by the impl trait, self type, or predicates
//    --> /Users/parno/.rustup/toolchains/1.93.0-aarch64-apple-darwin/lib/rustlib/src/rust/library/core/src/iter/adapters/map.rs:143:6
//     |
// 143 | impl<B, I: DoubleEndedIterator, F> DoubleEndedIterator for Map<I, F>
//     |      ^^^^^

// #[verifier::external_body]
// #[verifier::external_type_specification]
// #[verifier::reject_recursive_types(I)]
// #[verifier::reject_recursive_types(F)]
// pub struct ExMap<I, F>(core::iter::Map<I, F>)
    // // where 
    // //     I: Iterator + Sized,
    // //     F: FnMut(I::Item) -> B;
// ;

// B must be a type parameter of MyMap so that Verus can resolve Self::Item
// without producing TyKind::Infer (which causes a panic in mid_ty_to_vir_ghost).
pub struct MyMap<B, I, F>{ x: u64, y: I, z: F, w: core::marker::PhantomData<B> }

#[verifier::external]
impl<B, I, F> Iterator for MyMap<B, I, F>
    where
        I: Iterator,
        F: FnMut(I::Item) -> B,
{
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[verifier::external]
impl<B, I, F> DoubleEndedIterator for MyMap<B, I, F>
    where
        I: Iterator,
        F: FnMut(I::Item) -> B,
{
    #[verifier::external_body]
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

// Ghost accessor for the inner iterator
pub uninterp spec fn map_iter<B, I, F>(r: MyMap<B, I, F>) -> I;

// Ghost accessor for the inner function
pub uninterp spec fn map_fun<B, I, F>(r: MyMap<B, I, F>) -> F;

impl <B, I, F> IteratorSpecImpl for MyMap<B, I, F>
    where 
        I: Iterator + IteratorSpec, 
        F: FnMut(I::Item) -> B,
{

    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        map_iter(*self).obeys_prophetic_iter_laws()
    }

    #[verifier::prophetic]
    uninterp spec fn remaining(&self) -> Seq<Self::Item>; 

    #[verifier::prophetic]
    uninterp spec fn completes(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_inv(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& map_iter(*self).initial_value_inv(&map_iter(*init))
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        None
        // REVIEW: It would be nice to use a definition like the one below,
        //         but we don't have an output value to supply for ???
        //         We also can't reference `remaining` since its prophetic
        //         and `peek` is not
        // match map_iter(*self).peek(index) {
        //     Some(v) => Some(map_fun(*self).call_ensures((v,), ???),
        //     None => None,
        // }
    }
}

impl <B, I, F> DoubleEndedIteratorSpecImpl for MyMap<B, I, F>
    where I: DoubleEndedIterator + IteratorSpec,
          F: FnMut(I::Item) -> B,
{

    open spec fn peek_back(&self, index: int) -> Option<Self::Item> {
        None // REVIEW: See note above for `peek`
    }
}


// Spec version of I::map
pub uninterp spec fn into_map_spec<B, I, F>(i: I, f: F) -> MyMap<B, I, F>
    where
        I: Iterator + IteratorSpec, 
        F: FnMut(I::Item) -> B,
;

// Workaround issues with Verus support for default trait methods
#[verifier::external_body]
#[verifier::when_used_as_spec(into_map_spec)]
pub fn to_map<B, I, F>(i: I, f: F) -> (r: MyMap<B, I, F>)
    where
        I: Iterator + IteratorSpec, 
        F: FnMut(I::Item) -> B,
    requires
        i.obeys_prophetic_iter_laws(),
        forall |k| #![auto] 0 <= k < IteratorSpec::remaining(&i).len() ==> call_requires(f, (IteratorSpec::remaining(&i)[k], )),
        i.initial_value_inv(&i),
    ensures
        r == into_map_spec::<B, I, F>(i, f),
        IteratorSpec::remaining(&r).len() <= IteratorSpec::remaining(&i).len(),
        forall |k| #![auto] 0 <= k < IteratorSpec::remaining(&r).len() ==> call_ensures(f, (IteratorSpec::remaining(&i)[k],), IteratorSpec::remaining(&r)[k]),
        IteratorSpec::completes(&r) ==> IteratorSpec::completes(&i) && 
            IteratorSpec::remaining(&r).len() == IteratorSpec::remaining(&i).len(),
        IteratorSpec::decrease(&r) is Some == IteratorSpec::decrease(&i) is Some,
        IteratorSpec::initial_value_inv(&r, &r),
        map_iter(r) == i,
        map_fun(r) == f,
{
    todo!()
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


} // verus!
