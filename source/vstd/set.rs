#[allow(unused_imports)]
use super::iset::*;
#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// `Set<A>` is a finite set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.

//////////////////////////////////////////////////////////////////////////////
// Important soundness note!
//
// In this file, one can construct `Set`s directly with
// `Set{set:...}`, Since we make the assumption that all Sets are
// finite, we must be careful to only allow functions in this file
// that construct `Set`s to admit a finite number of elements.
// Otherwise, one could prove that set both finite and infinite and
// introduce false. The danger of this soundness risk is encapsulated
// in the axiom `lemma_set_is_finite`, which assumes that the set
// function is finite.
//
// Outside of this file, callers only have access to `Set`
// constructors that create only finite sets.
//
// For future work, we may figure out how to have `Set` use a
// `Seq`-like representation that is inherently finite, to eliminate
// this risk. We haven't done this yet, though, because it would
// introduce the problem of multiple representations of equivalent
// sets, which creates a different problem with extensional equality.
//////////////////////////////////////////////////////////////////////////////

#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A> {
    set: spec_fn(A) -> bool,
}

pub open spec fn set_function_finite<A>(f: spec_fn(A) -> bool) -> bool
{
    ISet::<A>::new(f).finite()
}

impl<A> Set<A> {
    /// The "empty" set.
    ///
    /// Usage Example: <br>
    /// ```rust
    /// let empty_set = Set::<A>::empty();
    ///
    /// assert(empty_set.is_empty());
    /// assert(empty_set.complement() =~= Set::<A>::full());
    /// assert(Set::<A>::empty().finite());
    /// assert(Set::<A>::empty().len() == 0);
    /// assert(forall |x: A| !Set::<A>::empty().contains(x));
    /// ```
    /// Axioms around the empty set are: <br>
    /// * [`lemma_set_empty_finite`]
    /// * [`lemma_set_empty_len`] <br>
    /// * [`lemma_set_empty`]
    #[rustc_diagnostic_item = "verus::vstd::set::Set::empty"]
    pub closed spec fn empty() -> Set<A> {
        Set { set: |a| false }
    }

    /// Set whose membership is determined by the given boolean predicate,
    /// but only if the predicate produces a finite set. (If it produces an
    /// infinite set, the result of this function is None.)
    ///
    /// Usage Examples:
    /// ```rust
    /// let set_a = Set::new(|x : nat| x < 42);
    /// let set_b = Set::<A>::new(|x| some_predicate(x));
    /// assert(set_function_finite(|x| some_predicate(x)) ==>
    ///        set_b matches Some(s) &&
    ///        forall|x| some_predicate(x) <==> s.contains(x));
    /// ```
    pub closed spec fn new(f: spec_fn(A) -> bool) -> Option<Set<A>> {
        if set_function_finite(f) {
            Some(Set { set: f })
        }
        else {
            None
        }
    }

    /// Set whose membership is determined by the given boolean predicate,
    /// assuming the predicate produces a finite set.
    ///
    /// Usage Examples:
    /// ```rust
    /// let set_a = Set::new_assuming_finite(|x : nat| x < 42);
    /// let set_b = Set::<A>::new_assuming_finite(|x| some_predicate(x));
    /// assert(forall|x| some_predicate(x) <==> set_b.contains(x));
    /// ```
    #[deprecated(note = "Set::new_assuming_finite is helpful for incremental porting of existing code to the new version of Verus supporting finite sets. But it's dangerous since it assumes the given function describes a finite set.")]
    pub closed spec fn new_assuming_finite(f: spec_fn(A) -> bool) -> Set<A> {
        Set { set: f }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that if `A` is infinite, then this produces None.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::full"]
    pub open spec fn full() -> Option<Set<A>> {
        Set::new(|a: A| true)
    }

    /// Predicate indicating if the set contains the given element.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::contains"]
    pub closed spec fn contains(self, a: A) -> bool {
        (self.set)(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    /// Returns `true` if the first argument is a subset of the second.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::subset_of"]
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::insert"]
    pub closed spec fn insert(self, a: A) -> Set<A> {
        Set {
            set: |a2|
                if a2 == a {
                    true
                } else {
                    (self.set)(a2)
                },
        }
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::remove"]
    pub closed spec fn remove(self, a: A) -> Set<A> {
        Set {
            set: |a2|
                if a2 == a {
                    false
                } else {
                    (self.set)(a2)
                },
        }
    }

    /// Union of two sets.
    pub closed spec fn union(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) || (s2.set)(a) }
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.
    pub closed spec fn intersect(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) && (s2.set)(a) }
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub closed spec fn difference(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) && !(s2.set)(a) }
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    /// Set complement (within the space of all possible elements in `A`).
    /// Returns None if this would be an infinite set.
    pub open spec fn complement(self) -> Option<Set<A>> {
        Set::new(|a| !self.contains(a))
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub closed spec fn filter(self, f: spec_fn(A) -> bool) -> Set<A> {
        Set { set: |a| (self.set)(a) && f(a) }
    }

    /// Returns `true` if the set is finite.
    #[deprecated(note = "Every Set is always finite, so this is always true.")]
    pub open spec fn finite(self) -> bool {
        true
    }

    /// Returns `true` if this set is congruent to (contains the same elements as)
    /// a given ISet.
    pub open spec fn congruent(self, s2: ISet<A>) -> bool {
        forall|a: A| self.contains(a) <==> s2.contains(a)
    }

    /// Generates an `iset` with the same elements
    pub open spec fn to_iset(self) -> ISet<A> {
        ISet::<A>::new(|a| self.contains(a))
    }

    /// Cardinality of the set.
    pub closed spec fn len(self) -> nat {
        self.fold(0, |acc: nat, a| acc + 1)
    }

    /// Chooses an arbitrary element of the set.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> A {
        choose|a: A| self.contains(a)
    }

    /// Creates a [`Map`] whose domain is the given set.
    /// The values of the map are given by `f`, a function of the keys.
    pub uninterp spec fn mk_map<V>(self, f: spec_fn(A) -> V) -> Map<A, V>;

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint(self, s2: Self) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

#[verifier::reject_recursive_types(A)]
pub struct FinitenessDemonstration<A>
{
    pub f: spec_fn(A) -> nat,
    pub ub: nat,
}

impl<A> FinitenessDemonstration<A>
{
    pub open spec fn demonstrates_set_is_finite(self, s: Set<A>) -> bool
    {
        &&& forall|a1, a2| #![all_triggers] s.contains(a1) && s.contains(a2) && a1 != a2 ==> (self.f)(a1) != (self.f)(a2)
        &&& forall|a| s.contains(a) ==> (self.f)(a) < self.ub
    }
}

impl<A> Set<A> {
    pub axiom fn axiom_get_finiteness_demonstration(self) -> (d: FinitenessDemonstration<A>)
        ensures
            d.demonstrates_set_is_finite(self),
    ;
}

pub mod fold {
    //! This module defines a fold function for finite sets and proves a number of associated
    //! lemmas.
    //!
    //! The module was ported (with some modifications) from Isabelle/HOL's finite set theory in:
    //! `HOL/Finite_Set.thy`
    //! That file contains the following author list:
    //!
    //!
    //! (*  Title:      HOL/Finite_Set.thy
    //!     Author:     Tobias Nipkow
    //!     Author:     Lawrence C Paulson
    //!     Author:     Markus Wenzel
    //!     Author:     Jeremy Avigad
    //!     Author:     Andrei Popescu
    //! *)
    //!
    //!
    //! The file is distributed under a 3-clause BSD license as indicated in the file `COPYRIGHT`
    //! in Isabelle's root directory, which also carries the following copyright notice:
    //!
    //! Copyright (c) 1986-2024,
    //! University of Cambridge,
    //! Technische Universitaet Muenchen,
    //! and contributors.
    use super::*;

    broadcast group group_set_lemmas_early {
        lemma_set_empty,
        lemma_set_new,
        lemma_set_insert_same,
        lemma_set_insert_different,
        lemma_set_remove_same,
        lemma_set_remove_insert,
        lemma_set_remove_different,
        lemma_set_union,
        lemma_set_intersect,
        lemma_set_difference,
        lemma_set_complement,
        lemma_set_ext_equal,
        lemma_set_ext_equal_deep,
    }

    pub open spec fn is_fun_commutative<A, B>(f: spec_fn(B, A) -> B) -> bool {
        forall|a1, a2, b| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2)
    }

    // This predicate is intended to be used like an inductive predicate, with the corresponding
    // introduction, elimination and induction rules proved below.
    #[verifier(opaque)]
    spec fn fold_graph<A, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A>, y: B, d: nat) -> bool
        decreases d,
    {
        if s == Set::empty() {
            &&& z == y
            &&& d == 0
        } else {
            exists|yr, a|
                {
                    &&& #[trigger] trigger_fold_graph(yr, a)
                    &&& d > 0
                    &&& s.contains(a)
                    &&& fold_graph(z, f, s.remove(a), yr, sub(d, 1))
                    &&& y == f(yr, a)
                }
        }
    }

    spec fn trigger_fold_graph<A, B>(yr: B, a: A) -> bool {
        true
    }

    // Introduction rules
    proof fn lemma_fold_graph_empty_intro<A, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            fold_graph(z, f, Set::empty(), z, 0),
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_intro<A, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A>,
        y: B,
        d: nat,
        a: A,
    )
        requires
            fold_graph(z, f, s, y, d),
            !s.contains(a),
        ensures
            fold_graph(z, f, s.insert(a), f(y, a), d + 1),
    {
        broadcast use group_set_lemmas_early;

        reveal(fold_graph);
        let _ = trigger_fold_graph(y, a);
        assert(s == s.insert(a).remove(a));
    }

    // Elimination rules
    proof fn lemma_fold_graph_empty_elim<A, B>(z: B, f: spec_fn(B, A) -> B, y: B, d: nat)
        requires
            fold_graph(z, f, Set::empty(), y, d),
        ensures
            z == y,
            d == 0,
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_elim<A, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A>,
        y: B,
        d: nat,
        a: A,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s.insert(a), y, d),
            !s.contains(a),
        ensures
            d > 0,
            exists|yp| y == f(yp, a) && #[trigger] fold_graph(z, f, s, yp, sub(d, 1)),
    {
        reveal(fold_graph);
        lemma_fold_graph_insert_elim_aux(z, f, s.insert(a), y, d, a);
        assert(s.insert(a).remove(a) =~= s);
        let yp = choose|yp| y == f(yp, a) && #[trigger] fold_graph(z, f, s, yp, sub(d, 1));
    }

    proof fn lemma_fold_graph_insert_elim_aux<A, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A>,
        y: B,
        d: nat,
        a: A,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
            s.contains(a),
        ensures
            exists|yp| y == f(yp, a) && #[trigger] fold_graph(z, f, s.remove(a), yp, sub(d, 1)),
        decreases d,
    {
        broadcast use group_set_lemmas_early;

        reveal(fold_graph);
        let (yr, aa): (B, A) = choose|yr, aa|
            #![all_triggers]
            {
                &&& trigger_fold_graph(yr, a)
                &&& d > 0
                &&& s.contains(aa)
                &&& fold_graph(z, f, s.remove(aa), yr, sub(d, 1))
                &&& y == f(yr, aa)
            };
        assert(trigger_fold_graph(yr, a));
        if s.remove(aa) == Set::empty() {
        } else {
            if a == aa {
            } else {
                lemma_fold_graph_insert_elim_aux(z, f, s.remove(aa), yr, sub(d, 1), a);
                let yrp = choose|yrp|
                    yr == f(yrp, a) && #[trigger] fold_graph(
                        z,
                        f,
                        s.remove(aa).remove(a),
                        yrp,
                        sub(d, 2),
                    );
                assert(fold_graph(z, f, s.remove(aa).insert(aa).remove(a), f(yrp, aa), sub(d, 1)))
                    by {
                    assert(s.remove(aa).remove(a) == s.remove(aa).insert(aa).remove(a).remove(aa));
                    assert(trigger_fold_graph(yrp, aa));
                };
            }
        }
    }

    // Induction rule
    proof fn lemma_fold_graph_induct<A, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A>,
        y: B,
        d: nat,
        pred: spec_fn(Set<A>, B, nat) -> bool,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
            pred(Set::empty(), z, 0),
            forall|a, s, y, d|
                pred(s, y, d) && !s.contains(a) && #[trigger] fold_graph(z, f, s, y, d) ==> pred(
                    #[trigger] s.insert(a),
                    f(y, a),
                    d + 1,
                ),
        ensures
            pred(s, y, d),
        decreases d,
    {
        broadcast use group_set_lemmas_early;

        reveal(fold_graph);
        if s == Set::empty() {
            lemma_fold_graph_empty_elim(z, f, y, d);
        } else {
            let a = s.choose();
            lemma_fold_graph_insert_elim(z, f, s.remove(a), y, d, a);
            let yp = choose|yp|
                y == f(yp, a) && #[trigger] fold_graph(z, f, s.remove(a), yp, sub(d, 1));
            lemma_fold_graph_induct(z, f, s.remove(a), yp, sub(d, 1), pred);
        }
    }

    impl<A> Set<A> {
        /// Folds the set, applying `f` to perform the fold. The next element for the fold is chosen by
        /// the choose operator.
        ///
        /// Given a set `s = {x0, x1, x2, ..., xn}`, applying this function `s.fold(init, f)`
        /// returns `f(...f(f(init, x0), x1), ..., xn)`.
        pub closed spec fn fold<B>(self, z: B, f: spec_fn(B, A) -> B) -> B
            recommends
                is_fun_commutative(f),
        {
            let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, self, y, d);
            y
        }
    }

    proof fn lemma_fold_graph_deterministic<A, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A>,
        y1: B,
        y2: B,
        d1: nat,
        d2: nat,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y1, d1),
            fold_graph(z, f, s, y2, d2),
        ensures
            y1 == y2,
            d1 == d2,
    {
        let pred = |s: Set<A>, y1: B, d1: nat|
            forall|y2, d2| fold_graph(z, f, s, y2, d2) ==> y1 == y2 && d2 == d1;
        // Base case
        assert(pred(Set::empty(), z, 0)) by {
            assert forall|y2, d2| fold_graph(z, f, Set::empty(), y2, d2) implies z == y2 && d2
                == 0 by {
                lemma_fold_graph_empty_elim(z, f, y2, d2);
            };
        };
        // Step case
        assert forall|a, s, y1, d1|
            pred(s, y1, d1) && !s.contains(a) && #[trigger] fold_graph(
                z,
                f,
                s,
                y1,
                d1,
            ) implies pred(#[trigger] s.insert(a), f(y1, a), d1 + 1) by {
            assert forall|y2, d2| fold_graph(z, f, s.insert(a), y2, d2) implies f(y1, a) == y2 && d2
                == d1 + 1 by {
                lemma_fold_graph_insert_elim(z, f, s, y2, d2, a);
            };
        };
        lemma_fold_graph_induct(z, f, s, y2, d2, pred);
    }

    proof fn lemma_fold_is_fold_graph<A, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A>, y: B, d: nat)
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.fold(z, f) == y,
    {
        if s.fold(z, f) != y {
            let (y2, d2) = choose|y2, d2| fold_graph(z, f, s, y2, d2) && y2 != y;
            lemma_fold_graph_deterministic(z, f, s, y2, y, d2, d);
            assert(false);
        }
    }

    // At this point set cardinality is not yet defined, so we can't easily give a decreasing
    // measure to prove the subsequent lemma `lemma_fold_graph_exists`. Instead, we first prove
    // this lemma, for which we use the upper bound of a finiteness witness as the decreasing
    // measure.
    pub proof fn lemma_finite_set_induct<A>(s: Set<A>, pred: spec_fn(Set<A>) -> bool)
        requires
            pred(Set::empty()),
            forall|other: Set<A>, a: A| pred(other) && !other.contains(a) ==> #[trigger] pred(other.insert(a)),
        ensures
            pred(s),
    {
        let FinitenessDemonstration{ f, ub } = s.axiom_get_finiteness_demonstration();
        lemma_finite_set_induct_aux(s, f, ub, pred);
    }

    proof fn lemma_finite_set_induct_aux<A>(
        s: Set<A>,
        f: spec_fn(A) -> nat,
        ub: nat,
        pred: spec_fn(Set<A>) -> bool,
    )
        requires
            forall|a1, a2| #![all_triggers] s.contains(a1) && s.contains(a2) && a1 != a2 ==> f(a1) != f(a2),
            forall|a| s.contains(a) ==> f(a) < ub,
            pred(Set::empty()),
            forall|other: Set<A>, a: A| pred(other) && !other.contains(a) ==> #[trigger] pred(other.insert(a)),
        ensures
            pred(s),
        decreases ub,
    {
        broadcast use group_set_lemmas_early;

        if s =~= Set::empty() {
        } else {
            let a = s.choose();
            // If `f` maps something to `ub - 1`, remap it to `f(a)` so we can decrease ub
            let fp = |aa|
                if f(aa) == ub - 1 {
                    f(a)
                } else {
                    f(aa)
                };
            lemma_finite_set_induct_aux(s.remove(a), fp, sub(ub, 1), pred);
        }
    }

    proof fn lemma_fold_graph_exists<A, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A>)
        requires
            is_fun_commutative(f),
        ensures
            exists|y, d| fold_graph(z, f, s, y, d),
    {
        let pred = |s| exists|y, d| fold_graph(z, f, s, y, d);
        // Base case
        assert(fold_graph(z, f, Set::empty(), z, 0)) by {
            lemma_fold_graph_empty_intro(z, f);
        };
        // Step case
        assert forall|other: Set<A>, a: A| pred(other) && !other.contains(a) implies #[trigger] pred(
            other.insert(a),
        ) by {
            let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, other, y, d);
            lemma_fold_graph_insert_intro(z, f, other, y, d, a);
        };
        lemma_finite_set_induct(s, pred);
    }

    pub broadcast proof fn lemma_fold_insert<A, B>(s: Set<A>, z: B, f: spec_fn(B, A) -> B, a: A)
        requires
            !s.contains(a),
            is_fun_commutative(f),
        ensures
            #[trigger] s.insert(a).fold(z, f) == f(s.fold(z, f), a),
    {
        lemma_fold_graph_exists(z, f, s);
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, s, y, d);
        lemma_fold_graph_insert_intro(z, f, s, s.fold(z, f), d, a);
        lemma_fold_is_fold_graph(z, f, s.insert(a), f(s.fold(z, f), a), d + 1);
    }

    pub broadcast proof fn lemma_fold_empty<A, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            #[trigger] Set::empty().fold(z, f) == z,
    {
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, Set::empty(), y, d);
        lemma_fold_graph_empty_intro(z, f);
        lemma_fold_graph_empty_elim(z, f, y, d);
    }

}

// Axioms
/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
}

pub broadcast proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    requires
        ISet::<A>::new(f).finite(),
    ensures
        Set::<A>::new(f) is Some,
        #[trigger] Set::<A>::new(f).unwrap().contains(a) == f(a),
{
    super::iset::lemma_iset_new(f, a);
}

pub broadcast proof fn lemma_set_new_some<A>(f: spec_fn(A) -> bool)
    requires
        ISet::<A>::new(f).finite(),
    ensures
        #[trigger] Set::<A>::new(f) is Some,
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,
{
    assert forall|aa| #![all_triggers] s.remove(a).insert(a).contains(aa) implies s.contains(
        aa,
    ) by {
        if a == aa {
        } else {
            lemma_set_remove_different(s, aa, a);
            lemma_set_insert_different(s.remove(a), aa, a);
        }
    };
    assert forall|aa| #![all_triggers] s.contains(aa) implies s.remove(a).insert(a).contains(
        aa,
    ) by {
        if a == aa {
            lemma_set_insert_same(s.remove(a), a);
        } else {
            lemma_set_remove_different(s, aa, a);
            lemma_set_insert_different(s.remove(a), aa, a);
        }
    };
    lemma_set_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn lemma_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_set_complement<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.complement().unwrap().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn lemma_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
    if s1 =~= s2 {
        assert(forall|a: A| s1.contains(a) == s2.contains(a));
    }
    if forall|a: A| s1.contains(a) == s2.contains(a) {
        if !(forall|a: A| #[trigger] (s1.set)(a) <==> (s2.set)(a)) {
            assert(exists|a: A| #[trigger] (s1.set)(a) != (s2.set)(a));
            let a = choose|a: A| #[trigger] (s1.set)(a) != (s2.set)(a);
            assert(s1.contains(a));
            assert(false);
        }
        assert(s1 =~= s2);
    }
}

pub broadcast proof fn lemma_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

pub broadcast axiom fn lemma_set_mk_map_domain<K, V>(s: Set<K>, f: spec_fn(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,
;

pub broadcast axiom fn lemma_set_mk_map_index<K, V>(s: Set<K>, f: spec_fn(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        #[trigger] s.mk_map(f)[key] == f(key),
;

// Trusted axioms about len
// Note: we could add more axioms about len, but they would be incomplete.
// The following, with lemma_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    fold::lemma_fold_empty(0, |b: nat, a: A| b + 1);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    if s.contains(a) {
        assert(s =~= s.insert(a));
    } else {
        fold::lemma_fold_insert(s, 0, |b: nat, a: A| b + 1, a);
    }
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_remove_len<A>(s: Set<A>, a: A)
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    lemma_set_insert_len(s.remove(a), a);
    if s.contains(a) {
        assert(s =~= s.remove(a).insert(a));
    } else {
        assert(s =~= s.remove(a));
    }
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_set_contains_len<A>(s: Set<A>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    let a = s.choose();
    assert(s.remove(a).insert(a) =~= s);
    lemma_set_insert_len(s.remove(a), a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A>(s: Set<A>)
    requires
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    // Separate statements to work around https://github.com/verus-lang/verusfmt/issues/86
    broadcast use lemma_set_contains_len;
    broadcast use lemma_set_empty_len;
    broadcast use lemma_set_ext_equal;

    let pred = |other: Set<A>| other.len() == 0 <==> other =~= Set::empty();
    fold::lemma_finite_set_induct(s, pred);
}

pub broadcast group group_set_lemmas {
    lemma_set_empty,
    lemma_set_new,
    lemma_set_new_some,
    lemma_set_insert_same,
    lemma_set_insert_different,
    lemma_set_remove_same,
    lemma_set_remove_insert,
    lemma_set_remove_different,
    lemma_set_union,
    lemma_set_intersect,
    lemma_set_difference,
    lemma_set_complement,
    lemma_set_ext_equal,
    lemma_set_ext_equal_deep,
    lemma_set_mk_map_domain,
    lemma_set_mk_map_index,
    lemma_set_empty_len,
    lemma_set_insert_len,
    lemma_set_remove_len,
    lemma_set_contains_len,
    lemma_set_choose_len,
    lemma_set_new,
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! set_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::set::Set::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! set {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::set::set_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;

} // verus!
