#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// `Set<A>` is a set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// In general, a set might be infinite.
/// To work specifically with finite sets, see the [`self.finite()`](Set::finite) predicate.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::full`] gives the set of all elements in `A`
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A> {
    set: spec_fn(A) -> bool,
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
    /// * [`axiom_set_empty_finite`](crate::set::axiom_set_empty_finite) <br>
    /// * [`axiom_set_empty_len`](crate::set::axiom_set_empty_len) <br>
    /// * [`axiom_set_empty`](crate::set::axiom_set_empty)
    #[rustc_diagnostic_item = "verus::vstd::set::Set::empty"]
    pub closed spec fn empty() -> Set<A> {
        Set { set: |a| false }
    }

    /// Set whose membership is determined by the given boolean predicate.
    ///
    /// Usage Examples:
    /// ```rust
    /// let set_a = Set::new(|x : nat| x < 42);
    /// let set_b = Set::<A>::new(|x| some_predicate(x));
    /// assert(forall|x| some_predicate(x) <==> set_b.contains(x));
    /// ```
    pub closed spec fn new(f: spec_fn(A) -> bool) -> Set<A> {
        Set {
            set: |a|
                if f(a) {
                    true
                } else {
                    false
                },
        }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::full"]
    pub open spec fn full() -> Set<A> {
        Set::empty().complement()
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
    pub closed spec fn complement(self) -> Set<A> {
        Set { set: |a| !(self.set)(a) }
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub open spec fn filter(self, f: spec_fn(A) -> bool) -> Set<A> {
        self.intersect(Self::new(f))
    }

    /// Returns `true` if the set is finite.
    pub closed spec fn finite(self) -> bool {
        exists|f: spec_fn(A) -> nat, ub: nat|
            {
                &&& #[trigger] trigger_finite(f, ub)
                &&& surj_on(f, self)
                &&& forall|a| self.contains(a) ==> f(a) < ub
            }
    }

    /// Cardinality of the set. (Only meaningful if a set is finite.)
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

// Closures make triggering finicky but using this to trigger explicitly works well.
spec fn trigger_finite<A>(f: spec_fn(A) -> nat, ub: nat) -> bool {
    true
}

spec fn surj_on<A, B>(f: spec_fn(A) -> B, s: Set<A>) -> bool {
    forall|a1, a2| #![all_triggers] s.contains(a1) && s.contains(a2) && a1 != a2 ==> f(a1) != f(a2)
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

    broadcast group group_set_axioms_early {
        axiom_set_empty,
        axiom_set_new,
        axiom_set_insert_same,
        axiom_set_insert_different,
        axiom_set_remove_same,
        axiom_set_remove_insert,
        axiom_set_remove_different,
        axiom_set_union,
        axiom_set_intersect,
        axiom_set_difference,
        axiom_set_complement,
        axiom_set_ext_equal,
        axiom_set_ext_equal_deep,
        axiom_set_empty_finite,
        axiom_set_insert_finite,
        axiom_set_remove_finite,
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
        if s === Set::empty() {
            &&& z == y
            &&& d == 0
        } else {
            exists|yr, a|
                {
                    &&& #[trigger] trigger_fold_graph(yr, a)
                    &&& d > 0
                    &&& s.remove(a).finite()
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
        broadcast use group_set_axioms_early;

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
        broadcast use group_set_axioms_early;

        reveal(fold_graph);
        let (yr, aa): (B, A) = choose|yr, aa|
            #![all_triggers]
            {
                &&& trigger_fold_graph(yr, a)
                &&& d > 0
                &&& s.remove(aa).finite()
                &&& s.contains(aa)
                &&& fold_graph(z, f, s.remove(aa), yr, sub(d, 1))
                &&& y == f(yr, aa)
            };
        assert(trigger_fold_graph(yr, a));
        if s.remove(aa) === Set::empty() {
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
        broadcast use group_set_axioms_early;

        reveal(fold_graph);
        if s === Set::empty() {
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
                self.finite(),
                is_fun_commutative(f),
        {
            let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, self, y, d);
            y
        }
    }

    proof fn lemma_fold_graph_finite<A, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A>, y: B, d: nat)
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.finite(),
    {
        broadcast use group_set_axioms_early;

        let pred = |s: Set<A>, y, d| s.finite();
        lemma_fold_graph_induct(z, f, s, y, d, pred);
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
        lemma_fold_graph_finite(z, f, s, y, d);
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
            s.finite(),
            pred(Set::empty()),
            forall|s, a| pred(s) && s.finite() && !s.contains(a) ==> #[trigger] pred(s.insert(a)),
        ensures
            pred(s),
    {
        let (f, ub) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
            trigger_finite(f, ub) && surj_on(f, s) && (forall|a| s.contains(a) ==> f(a) < ub);
        lemma_finite_set_induct_aux(s, f, ub, pred);
    }

    proof fn lemma_finite_set_induct_aux<A>(
        s: Set<A>,
        f: spec_fn(A) -> nat,
        ub: nat,
        pred: spec_fn(Set<A>) -> bool,
    )
        requires
            surj_on(f, s),
            s.finite(),
            forall|a| s.contains(a) ==> f(a) < ub,
            pred(Set::empty()),
            forall|s, a| pred(s) && s.finite() && !s.contains(a) ==> #[trigger] pred(s.insert(a)),
        ensures
            pred(s),
        decreases ub,
    {
        broadcast use group_set_axioms_early;

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
            s.finite(),
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
        assert forall|s, a| pred(s) && s.finite() && !s.contains(a) implies #[trigger] pred(
            s.insert(a),
        ) by {
            let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, s, y, d);
            lemma_fold_graph_insert_intro(z, f, s, y, d, a);
        };
        lemma_finite_set_induct(s, pred);
    }

    pub broadcast proof fn lemma_fold_insert<A, B>(s: Set<A>, z: B, f: spec_fn(B, A) -> B, a: A)
        requires
            s.finite(),
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
pub broadcast proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
pub broadcast proof fn axiom_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] Set::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
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
            axiom_set_remove_different(s, aa, a);
            axiom_set_insert_different(s.remove(a), aa, a);
        }
    };
    assert forall|aa| #![all_triggers] s.contains(aa) implies s.remove(a).insert(a).contains(
        aa,
    ) by {
        if a == aa {
            axiom_set_insert_same(s.remove(a), a);
        } else {
            axiom_set_remove_different(s, aa, a);
            axiom_set_insert_different(s.remove(a), aa, a);
        }
    };
    axiom_set_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
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

pub broadcast proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

pub broadcast axiom fn axiom_mk_map_domain<K, V>(s: Set<K>, f: spec_fn(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,
;

pub broadcast axiom fn axiom_mk_map_index<K, V>(s: Set<K>, f: spec_fn(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        #[trigger] s.mk_map(f)[key] == f(key),
;

// Trusted axioms about finite
/// The empty set is finite.
pub broadcast proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
pub broadcast proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    let (f, ub) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
        trigger_finite(f, ub) && surj_on(f, s) && (forall|a| s.contains(a) ==> f(a) < ub);
    let f2 = |a2: A|
        if a2 == a {
            ub
        } else {
            f(a2)
        };
    let ub2 = ub + 1;
    let _ = trigger_finite(f2, ub2);
    assert forall|a1, a2|
        #![all_triggers]
        s.insert(a).contains(a1) && s.insert(a).contains(a2) && a1 != a2 implies f2(a1) != f2(
        a2,
    ) by {
        if a != a1 {
            assert(s.contains(a1));
        }
        if a != a2 {
            assert(s.contains(a2));
        }
    };
    assert forall|a2| s.insert(a).contains(a2) implies #[trigger] f2(a2) < ub2 by {
        if a == a2 {
        } else {
            assert(s.contains(a2));
        }
    };
}

/// The result of removing an element `a` from a finite set `s` is also finite.
pub broadcast proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    let (f, ub) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
        trigger_finite(f, ub) && surj_on(f, s) && (forall|a| s.contains(a) ==> f(a) < ub);
    assert forall|a1, a2|
        #![all_triggers]
        s.remove(a).contains(a1) && s.remove(a).contains(a2) && a1 != a2 implies f(a1) != f(a2) by {
        if a != a1 {
            assert(s.contains(a1));
        }
        if a != a2 {
            assert(s.contains(a2));
        }
    };
    assert(surj_on(f, s.remove(a)));
    assert forall|a2| s.remove(a).contains(a2) implies #[trigger] f(a2) < ub by {
        if a == a2 {
        } else {
            assert(s.contains(a2));
        }
    };
}

/// The union of two finite sets is finite.
pub broadcast proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
    let (f1, ub1) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
        trigger_finite(f, ub) && surj_on(f, s1) && (forall|a| s1.contains(a) ==> f(a) < ub);
    let (f2, ub2) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
        trigger_finite(f, ub) && surj_on(f, s2) && (forall|a| s2.contains(a) ==> f(a) < ub);
    let f3 = |a|
        if s1.contains(a) {
            f1(a)
        } else {
            ub1 + f2(a)
        };
    let ub3 = ub1 + ub2;
    assert(trigger_finite(f3, ub3));
    assert(forall|a|
        #![all_triggers]
        s1.union(s2).contains(a) ==> s1.contains(a) || s2.contains(a));
}

/// The intersection of two finite sets is finite.
pub broadcast proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
    assert(forall|a|
        #![all_triggers]
        s1.intersect(s2).contains(a) ==> s1.contains(a) && s2.contains(a));
}

/// The set difference between two finite sets is finite.
pub broadcast proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
    assert(forall|a|
        #![all_triggers]
        s1.difference(s2).contains(a) ==> s1.contains(a) && !s2.contains(a));
}

/// An infinite set `s` contains the element `s.choose()`.
pub broadcast proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

// Trusted axioms about len
// Note: we could add more axioms about len, but they would be incomplete.
// The following, with axiom_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    fold::lemma_fold_empty(0, |b: nat, a: A| b + 1);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
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
pub broadcast proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    axiom_set_remove_finite(s, a);
    axiom_set_insert_len(s.remove(a), a);
    if s.contains(a) {
        assert(s =~= s.remove(a).insert(a));
    } else {
        assert(s =~= s.remove(a));
    }
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn axiom_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    let a = s.choose();
    assert(s.remove(a).insert(a) =~= s);
    axiom_set_remove_finite(s, a);
    axiom_set_insert_finite(s.remove(a), a);
    axiom_set_insert_len(s.remove(a), a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    // Separate statements to work around https://github.com/verus-lang/verusfmt/issues/86
    broadcast use axiom_set_contains_len;
    broadcast use axiom_set_empty_len;
    broadcast use axiom_set_ext_equal;
    broadcast use axiom_set_insert_finite;

    let pred = |s: Set<A>| s.finite() ==> s.len() == 0 <==> s =~= Set::empty();
    fold::lemma_finite_set_induct(s, pred);
}

pub broadcast group group_set_axioms {
    axiom_set_empty,
    axiom_set_new,
    axiom_set_insert_same,
    axiom_set_insert_different,
    axiom_set_remove_same,
    axiom_set_remove_insert,
    axiom_set_remove_different,
    axiom_set_union,
    axiom_set_intersect,
    axiom_set_difference,
    axiom_set_complement,
    axiom_set_ext_equal,
    axiom_set_ext_equal_deep,
    axiom_mk_map_domain,
    axiom_mk_map_index,
    axiom_set_empty_finite,
    axiom_set_insert_finite,
    axiom_set_remove_finite,
    axiom_set_union_finite,
    axiom_set_intersect_finite,
    axiom_set_difference_finite,
    axiom_set_choose_finite,
    axiom_set_empty_len,
    axiom_set_insert_len,
    axiom_set_remove_len,
    axiom_set_contains_len,
    axiom_set_choose_len,
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::set::set_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;

} // verus!
