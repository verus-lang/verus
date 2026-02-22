#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use core::marker::PhantomData;

verus! {

pub struct Finite;

pub struct Infinite;

pub trait Finiteness {
    // Let proofs learn an SMT value for the type finiteness, for example so one can
    // write spec fns that condition on the type.
    spec fn type_is_finite() -> bool;
}

// What keeps an adversary from introducing a new Finiteness to break these definitions?
impl Finiteness for Finite {
    open spec fn type_is_finite() -> bool {
        true
    }
}

impl Finiteness for Infinite {
    open spec fn type_is_finite() -> bool {
        false
    }
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct GSet<A, FINITE: Finiteness> {
    pub set: spec_fn(A) -> bool,
    pub _phantom: PhantomData<FINITE>,
}

//////////////////////////////////////////////////////////////////////////////
// Important soundness note!
//
// In this file, one can construct GSets directly with GSet{set:...}.
// Doing so for ISet is always sound, but when the type is Set (FINITE=Finite),
// we must be careful to only allow the set function to admit a finite number
// of elements. Otherwise, one could prove that set both finite and infinite
// and introduce false. The danger of this soundness risk is encapsulated
// in lemma_gset_finite_from_type, which assumes that the set function is finite.
//
// Outside of this file, callers only have access to Set constructors that
// create only finite sets.
//
// For future work, we may figure out how to have Set use a seq-like
// representation that is inherently finite to eliminate this risk. (However,
// that introduces the problem of multiple representations of equivalent
// sets, which creates a different problem with extensional equality.)
//////////////////////////////////////////////////////////////////////////////

pub broadcast proof fn axiom_gset_finite_from_trait<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        FINITE::type_is_finite(),
    ensures
        #[trigger] s.finite(),
{
    // This lemma is the root of the soundness danger (see "Important soundness note" above).
    admit();
}

pub broadcast proof fn lemma_gset_finite_from_type<A>(s: GSet<A, Finite>)
    ensures
        #[trigger] s.finite(),
{
    axiom_gset_finite_from_trait(s);
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    // `congruent` is an analog of extensional equality that is meaningful across types with mismatched
    // (or unknown) <FINITE> arguments. If two sets are congruent, then they have the same finiteness
    // and the same len(). We anticipate that `congruent` reasoning will mostly be used in library
    // code, where we're trying to generalize over the FINITE argument, and hence it's not exposed to
    // users through group lemma automation. We expect most user code will stay within Set or ISet,
    // where extensionality is the more natural concept and syntax. Hence, the lemmas aren't
    // part of the exported broadcast group.
    pub open spec fn congruent<FINITE2: Finiteness>(
        self: GSet<A, FINITE>,
        s2: GSet<A, FINITE2>,
    ) -> bool {
        forall|a: A| self.contains(a) <==> s2.contains(a)
    }

    pub broadcast proof fn congruent_infiniteness<FINITE2: Finiteness>(
        self: GSet<A, FINITE>,
        s2: GSet<A, FINITE2>,
    )
        requires
            #[trigger] self.congruent(s2),
        ensures
            self.finite() <==> s2.finite(),
    {
        broadcast use GSet::cast_finiteness_properties;

    }

    pub broadcast proof fn congruent_len<FINITE2: Finiteness>(
        self: GSet<A, FINITE>,
        s2: GSet<A, FINITE2>,
    )
        requires
            #[trigger] self.congruent(s2),
            self.finite(),
        ensures
            self.len() == s2.len(),
        decreases self.len(),
    {
        broadcast use {
            lemma_gset_empty_len,
            lemma_gset_len_empty,
            lemma_gset_remove_len,
            lemma_gset_remove_finite,
            lemma_gset_choose_len,
            lemma_gset_ext_equal,
        };

        if self == GSet::<A, FINITE>::empty() {
            assert(s2 =~= GSet::<A, FINITE2>::empty());  // trigger extn to get lemma_gset_empty_len
        } else {
            let x = self.choose();
            assert forall|a| self.remove(x).contains(a) == s2.remove(x).contains(a) by {
                if a != x {
                    assert(self.remove(x).contains(a) == self.contains(a));
                }
            }
            self.remove(x).congruent_len(s2.remove(x));
        }
    }

    // This map function is sound for finite sets because of `lemma_gset_map_finite`,
    // but we don't need to invoke that lemma here because this file is trusting
    // GSet constructors to do so soundly (see "Important soundness note" above).
    /// Returns the set that contains an element `f(x)` for every element `x` in `self`.
    pub open spec fn map<B>(self, f: spec_fn(A) -> B) -> GSet<B, FINITE> {
        GSet { set: |a: B| exists|x: A| self.contains(x) && a == f(x), _phantom: PhantomData }
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    /// Preserves finiteness of self.
    pub open spec fn filter(self, f: spec_fn(A) -> bool) -> (out: GSet<A, FINITE>) {
        GSet { set: |a| self.contains(a) && f(a), _phantom: PhantomData }
    }

    /// Replace each element of a set with the elements of another set.
    /// Preserves finiteness of self.
    pub open spec fn product<B>(self, f: spec_fn(A) -> GSet<B, FINITE>) -> (out: GSet<
        B,
        FINITE,
    >) {
        GSet { set: |b| exists|a| self.contains(a) && f(a).contains(b), _phantom: PhantomData }
    }

    // This spec and its axioms encode the idea that an SMT .finite() ISet can be cast to a finite
    // Set, and anything can be cast to an ISet.
    pub uninterp spec fn cast_finiteness<NEWFINITE: Finiteness>(self) -> GSet<A, NEWFINITE>;

    pub open spec fn castable<NEWFINITE: Finiteness>(self) -> bool {
        self.finite() || !NEWFINITE::type_is_finite()
    }

    pub broadcast axiom fn cast_finiteness_properties<NEWFINITE: Finiteness>(self)
        requires
            self.castable::<NEWFINITE>(),
        ensures
            (#[trigger] self.cast_finiteness::<NEWFINITE>()).congruent(self),
    ;

    #[verifier::inline]
    pub open spec fn to_finite(self) -> GSet<A, Finite>
        recommends
            self.finite(),
    {
        self.cast_finiteness::<Finite>()
    }

    /// Identity rule for casting: It's always okay to cast back to the same type we started out as.
    /// (Only relevant for code that's generic over Finiteness.)
    pub broadcast proof fn lemma_self_castable(self)
        ensures
            #[trigger] self.castable::<FINITE>(),
    {
        if FINITE::type_is_finite() {
            axiom_gset_finite_from_trait(self);
        }
        self.cast_finiteness_properties::<FINITE>();
    }

    /// to_infinite "remembers" that it can be cast back to its original Finiteness.
    /// (Only relevant for code that's generic over Finiteness.)
    pub broadcast proof fn lemma_to_infinite_castable(self)
        requires
            self.castable::<FINITE>(),
        ensures
            #[trigger] self.to_infinite().castable::<FINITE>(),
    {
        self.cast_finiteness_properties::<FINITE>();
        self.to_infinite().cast_finiteness_properties::<FINITE>();
    }
}

pub broadcast proof fn lemma_gset_map_contains<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
}

pub broadcast proof fn lemma_gset_map_subset<A, FINITE1: Finiteness, FINITE2: Finiteness, B>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
    f: spec_fn(A) -> B,
)
    requires
        s1.subset_of(s2),
    ensures
        #![trigger s1.map(f), s2.map(f)]
        s1.map(f).subset_of(s2.map(f)),
{
}

pub broadcast proof fn lemma_gset_map_finite<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.map(f))]
        s.map(f).finite(),
{
    // Learn finiteness witness for original set `s`.
    let (ff, ub) = choose|ff: spec_fn(A) -> nat, ub: nat|
        {
            &&& #[trigger] trigger_finite(ff, ub)
            &&& surj_on(ff, s)
            &&& forall|a| s.contains(a) ==> ff(a) < ub
        };

    // converte the finite witness `f` for `s` into one for `s.map(s)` by mapping `b`s back through
    // f-inverse to get `a`s we can feed to `f`.
    let g = |b: B| ff(choose|a| s.contains(a) && b == f(a));
    assert(trigger_finite(g, ub));  // tickle spec fn finite trigger
}

pub broadcast proof fn lemma_gset_filter_finite<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> bool,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.filter(f))]
        s.filter(f).finite(),
{
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    pub open spec fn to_infinite(self) -> (infinite_out: GSet<A, Infinite>) {
        GSet { set: |a| self.contains(a), _phantom: PhantomData }
    }

    proof fn to_infinite_len(self)
        requires
            self.finite(),
        ensures
            self.len() == self.to_infinite().len(),
        decreases self.len(),
    {
        broadcast use lemma_gset_remove_len;
        broadcast use lemma_gset_choose_infinite;
        broadcast use lemma_gset_choose_len;
        broadcast use lemma_gset_empty_len;
        broadcast use lemma_gset_len_empty;

        if self.len() == 0 {
            assert(self.to_infinite() =~= GSet::empty());
        } else {
            let a = self.choose();
            lemma_gset_remove_finite(self, a);
            assert(self.to_infinite().remove(a) == self.remove(a).to_infinite());
            self.remove(a).to_infinite_len();
        }
    }

    pub broadcast proof fn to_infinite_ensures(self)
        requires
            self.finite(),
        ensures
            #![trigger self.to_infinite()]
            forall|a: A|
                self.contains(a) <==> #[trigger] self.to_infinite().contains(a),
            self.len() == self.to_infinite().len(),
            self.to_infinite().finite(),
    {
        self.to_infinite_len()
    }
}
// Closures make triggering finicky but using this to trigger explicitly works well.
pub open spec fn trigger_finite<A>(f: spec_fn(A) -> nat, ub: nat) -> bool {
    true
}

pub open spec fn surj_on<A, AFINITE: Finiteness, B>(f: spec_fn(A) -> B, s: GSet<A, AFINITE>) -> bool {
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

    pub(crate) broadcast group group_set_lemmas_early {
        GSet::cast_finiteness_properties,
        lemma_gset_finite_from_type,
        lemma_gset_generic_union,
        lemma_gset_generic_intersect,
        lemma_gset_generic_difference,
        lemma_gset_ext_equal,
        lemma_gset_ext_equal_deep,
        lemma_gset_insert_finite,
        lemma_gset_remove_finite,
    }

    pub open spec fn is_fun_commutative<A, B>(f: spec_fn(B, A) -> B) -> bool {
        forall|a1, a2, b| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2)
    }

    spec fn fold_graph_inner<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
        y: B,
        d: nat,
        yr: B,
        a: A,
    ) -> bool
        decreases d, 0int,
    {
        &&& #[trigger] trigger_fold_graph(yr, a)
        &&& d > 0
        &&& s.remove(a).finite()
        &&& s.contains(a)
        &&& fold_graph(z, f, s.remove(a), yr, sub(d, 1))
        &&& y == f(yr, a)
    }

    // This predicate is intended to be used like an inductive predicate, with the corresponding
    // introduction, elimination and induction rules proved below.
    #[verifier(opaque)]
    spec fn fold_graph<A, FINITE: Finiteness, B>(
        z: B,  // zero element
        f: spec_fn(B, A) -> B,  // graph of nodes (B) and directed edges (A) that lead from f(b,a) ~> b
        s: GSet<A, FINITE>,  // set of edges available to follow towards z
        y: B,  // A starting point for the fold
        d: nat,  // Number of steps left to reach zero
    ) -> bool
        decreases d, 1int,
    {
        if s === GSet::empty() {
            // This configuration can fold if we're already at zero (y==z and no steps) or ...
            &&& z == y
            &&& d == 0
        } else {
            // There is an edge (y,a) -> yr, a step closer to d, that satisfies fold_graph
            // without revisiting edge a.
            exists|yr, a|
                {
                    &&& #[trigger] trigger_fold_graph(yr, a)
                    &&& fold_graph_inner(z, f, s, y, d, yr, a)
                }
        }
    }

    spec fn trigger_fold_graph<A, B>(yr: B, a: A) -> bool {
        true
    }

    // Introduction rules
    proof fn lemma_fold_graph_empty_intro<A, FINITE: Finiteness, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            fold_graph(z, f, GSet::<A, FINITE>::empty(), z, 0),
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_intro<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
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
        broadcast use {group_set_lemmas_early, GSet::cast_finiteness_properties};

        reveal(fold_graph);
        let _ = trigger_fold_graph(y, a);
        assert(s == s.insert(a).remove(a));  // trigger
    }

    // Elimination rules
    proof fn lemma_fold_graph_empty_elim<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        y: B,
        d: nat,
    )
        requires
            fold_graph(z, f, GSet::<A, FINITE>::empty(), y, d),
        ensures
            z == y,
            d == 0,
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_elim<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
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

    proof fn lemma_fold_graph_insert_elim_aux<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
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
                &&& fold_graph_inner(z, f, s, y, d, yr, aa)
            };
        if s.remove(aa) === GSet::empty() {
            if !(s === GSet::empty()) {
                assert(exists|yr, a| #[trigger]
                    trigger_fold_graph(yr, a) && fold_graph_inner(z, f, s, y, d, yr, a));
                let (jyr, ja): (B, A) = choose|jyr, ja| #[trigger]
                    trigger_fold_graph(yr, a) && fold_graph_inner(z, f, s, y, d, jyr, ja);
                assert(fold_graph(z, f, s.remove(ja), jyr, sub(d, 1)));
            }
        } else {
            assert(exists|yr, a| #[trigger]
                trigger_fold_graph(yr, a) && fold_graph_inner(z, f, s, y, d, yr, a));
            if a != aa {
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
    proof fn lemma_fold_graph_induct<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
        y: B,
        d: nat,
        pred: spec_fn(GSet<A, FINITE>, B, nat) -> bool,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
            pred(GSet::empty(), z, 0),
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
        if s === GSet::empty() {
            lemma_fold_graph_empty_elim::<A, FINITE, B>(z, f, y, d);
        } else {
            let a = s.choose();
            lemma_fold_graph_insert_elim(z, f, s.remove(a), y, d, a);
            let yp = choose|yp|
                y == f(yp, a) && #[trigger] fold_graph(z, f, s.remove(a), yp, sub(d, 1));
            assert(pred(GSet::empty(), z, 0));  // flaky trigger failure?
            lemma_fold_graph_induct::<A, FINITE, B>(z, f, s.remove(a), yp, sub(d, 1), pred);
        }
    }

    impl<A, FINITE: Finiteness> GSet<A, FINITE> {
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

    proof fn lemma_fold_graph_finite<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
        y: B,
        d: nat,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.finite(),
    {
        broadcast use {group_set_lemmas_early, GSet::cast_finiteness_properties};

        let pred = |s: GSet<A, FINITE>, y, d| s.finite();
        lemma_fold_graph_induct::<A, FINITE, B>(z, f, s, y, d, pred);
    }

    proof fn lemma_fold_graph_deterministic<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
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
        let pred = |s: GSet<A, FINITE>, y1: B, d1: nat|
            forall|y2, d2| fold_graph(z, f, s, y2, d2) ==> y1 == y2 && d2 == d1;
        // Base case
        assert(pred(GSet::empty(), z, 0)) by {
            assert forall|y2, d2| fold_graph(z, f, GSet::<A, FINITE>::empty(), y2, d2) implies z
                == y2 && d2 == 0 by {
                lemma_fold_graph_empty_elim::<A, FINITE, B>(z, f, y2, d2);
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
        lemma_fold_graph_induct::<A, FINITE, B>(z, f, s, y2, d2, pred);
    }

    proof fn lemma_fold_is_fold_graph<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
        y: B,
        d: nat,
    )
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.fold(z, f) == y,
    {
        lemma_fold_graph_finite::<A, FINITE, B>(z, f, s, y, d);
        if s.fold(z, f) != y {
            let (y2, d2) = choose|y2, d2| fold_graph(z, f, s, y2, d2) && y2 != y;
            lemma_fold_graph_deterministic::<A, FINITE, B>(z, f, s, y2, y, d2, d);
            assert(false);
        }
    }

    // At this point set cardinality is not yet defined, so we can't easily give a decreasing
    // measure to prove the subsequent lemma `lemma_fold_graph_exists`. Instead, we first prove
    // this lemma, for which we use the upper bound of a finiteness witness as the decreasing
    // measure.
    pub proof fn lemma_finite_set_induct<A, FINITE: Finiteness>(
        s: GSet<A, FINITE>,
        pred: spec_fn(GSet<A, FINITE>) -> bool,
    )
        requires
            s.finite(),
            pred(GSet::empty()),
            forall|s, a| pred(s) && s.finite() && !s.contains(a) ==> #[trigger] pred(s.insert(a)),
        ensures
            pred(s),
    {
        let (f, ub) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
            trigger_finite(f, ub) && surj_on(f, s) && (forall|a| s.contains(a) ==> f(a) < ub);
        lemma_finite_set_induct_aux(s, f, ub, pred);
    }

    proof fn lemma_finite_set_induct_aux<A, FINITE: Finiteness>(
        s: GSet<A, FINITE>,
        f: spec_fn(A) -> nat,
        ub: nat,
        pred: spec_fn(GSet<A, FINITE>) -> bool,
    )
        requires
            surj_on(f, s),
            s.finite(),
            forall|a| s.contains(a) ==> f(a) < ub,
            pred(GSet::empty()),
            forall|s, a| pred(s) && s.finite() && !s.contains(a) ==> #[trigger] pred(s.insert(a)),
        ensures
            pred(s),
        decreases ub,
    {
        broadcast use group_set_lemmas_early;

        if s =~= GSet::empty() {
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

    proof fn lemma_fold_graph_exists<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
    )
        requires
            s.finite(),
            is_fun_commutative(f),
        ensures
            exists|y, d| fold_graph(z, f, s, y, d),
    {
        let pred = |s| exists|y, d| fold_graph(z, f, s, y, d);
        // Base case
        assert(fold_graph(z, f, GSet::<A, FINITE>::empty(), z, 0)) by {
            lemma_fold_graph_empty_intro::<A, FINITE, B>(z, f);
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

    pub broadcast proof fn lemma_fold_insert<A, FINITE: Finiteness, B>(
        s: GSet<A, FINITE>,
        z: B,
        f: spec_fn(B, A) -> B,
        a: A,
    )
        requires
            s.finite(),
            !s.contains(a),
            is_fun_commutative(f),
        ensures
            #[trigger] s.insert(a).fold(z, f) == f(s.fold(z, f), a),
    {
        lemma_fold_graph_exists::<A, FINITE, B>(z, f, s);
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, s, y, d);
        lemma_fold_graph_insert_intro(z, f, s, s.fold(z, f), d, a);
        lemma_fold_is_fold_graph::<A, FINITE, B>(z, f, s.insert(a), f(s.fold(z, f), a), d + 1);
    }

    pub broadcast proof fn lemma_fold_empty<A, FINITE: Finiteness, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            #[trigger] GSet::<A, FINITE>::empty().fold(z, f) == z,
    {
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, GSet::<A, FINITE>::empty(), y, d);
        lemma_fold_graph_empty_intro::<A, FINITE, B>(z, f);
        lemma_fold_graph_empty_elim::<A, FINITE, B>(z, f, y, d);
    }

}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_gset_generic_union<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_gset_generic_intersect<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_gset_generic_difference<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn lemma_gset_ext_equal<A, FINITE: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE>,
)
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

pub broadcast proof fn lemma_gset_ext_equal_deep<A, FINITE: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE>,
)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

pub broadcast proof fn lemma_gset_insert_finite<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    broadcast use GSet::cast_finiteness_properties;

    lemma_gset_finite_from_type(s.to_finite().insert(a));
    lemma_congruence_extensionality(s, s.to_finite());
    s.to_finite().insert(a).congruent_infiniteness(s.insert(a));
}

/// The result of removing an element `a` from a finite set `s` is also finite.
/// This conclusion is automatic for finite `Set`s, but still useful for SMT-`.finite()` `ISet`s.
pub broadcast proof fn lemma_gset_remove_finite<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    broadcast use GSet::cast_finiteness_properties;

    lemma_gset_finite_from_type(s.to_finite().remove(a));
    lemma_congruence_extensionality(s, s.to_finite());
    s.to_finite().remove(a).congruent_infiniteness(s.remove(a));
}

// Many proofs go through for free when we have equality of the representation .set field,
// but need per-element manual triggers for .contains if we only have congruence. So we
// use this lemma to keep them easy. However, end users don't get access to the .set field;
// I think this failure of triggeriness is similar to why it's more painful to talk about
// built-up Sets than function-constructed ISets.
pub proof fn lemma_congruence_extensionality<A, F1: Finiteness, F2: Finiteness>(
    x: GSet<A, F1>,
    y: GSet<A, F2>,
)
    requires
        x.congruent(y),
    ensures
        x.set == y.set,
{
    // Trigger our way through .contains
    assert forall|e| #[trigger] (x.set)(e) implies (y.set)(e) by {
        assert(y.contains(e));
    }

    assert forall|e| #[trigger] (y.set)(e) implies (x.set)(e) by {
        assert(x.contains(e));
    }
}

pub broadcast proof fn lemma_gset_generic_union_finite<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.generic_union(s2).finite(),
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
        s1.generic_union(s2).contains(a) ==> s1.contains(a) || s2.contains(a));
}

pub broadcast proof fn lemma_gset_generic_intersect_finite<
    A,
    FINITE1: Finiteness,
    FINITE2: Finiteness,
>(s1: GSet<A, FINITE1>, s2: GSet<A, FINITE2>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.generic_intersect(s2).finite(),
{
    assert(forall|a|
        #![all_triggers]
        s1.generic_intersect(s2).contains(a) ==> s1.contains(a) && s2.contains(a));
}


pub broadcast proof fn lemma_gset_generic_difference_finite<
    A,
    FINITE1: Finiteness,
    FINITE2: Finiteness,
>(s1: GSet<A, FINITE1>, s2: GSet<A, FINITE2>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.generic_difference(s2).finite(),
{
    assert(forall|a|
        #![all_triggers]
        s1.generic_difference(s2).contains(a) ==> s1.contains(a) && !s2.contains(a));
}

pub broadcast proof fn lemma_gset_choose_infinite<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

//////////////////////////////////////////////////////////////////////////////
// len lemmas
//////////////////////////////////////////////////////////////////////////////
// The following, with lemma_gset_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn lemma_gset_empty_len<A, FINITE: Finiteness>()
    ensures
        #[trigger] GSet::<A, FINITE>::empty().len() == 0,
{
    fold::lemma_fold_empty::<A, FINITE, nat>(0, |b: nat, a: A| b + 1);
}

pub broadcast proof fn lemma_gset_map_insert<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    broadcast use lemma_gset_ext_equal;

    assert(s.map(f).insert(f(a)) =~= s.insert(a).map(f)) by {
        assert forall|x| s.map(f).insert(f(a)).contains(x) implies s.insert(a).map(f).contains(
            x,
        ) by {
            let prex = if x == f(a) {
                a
            } else {
                choose|prex| s.contains(prex) && x == f(prex)
            };
            assert(s.insert(a).contains(prex) && x == f(prex));
        }
        assert forall|x| s.insert(a).map(f).contains(x) implies s.map(f).insert(f(a)).contains(
            x,
        ) by {
            let prex = choose|prex| s.insert(a).contains(prex) && x == f(prex);
            if prex != a {
                assert(s.contains(prex) && f(prex) == x);
            }
        }
    }
}

pub broadcast proof fn lemma_gset_map_len<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.map(f))]
        s.map(f).len() <= s.len(),
    decreases s.len(),
{
    broadcast use lemma_gset_empty_len;
    broadcast use lemma_gset_choose_len;
    broadcast use lemma_gset_len_empty;
    broadcast use lemma_gset_remove_finite;
    broadcast use lemma_gset_remove_len;
    broadcast use lemma_gset_map_finite;
    broadcast use lemma_gset_insert_len;
    broadcast use lemma_gset_map_insert;

    if s == GSet::<A, FINITE>::empty() {
        assert(s.map(f) == GSet::<B, FINITE>::empty());  // trigger lemma_gset_empty_len
    } else {
        let e = s.choose();
        let ps = s.remove(e);
        lemma_gset_map_len(ps, f);  // broadcast use would create recursion at this call site
        assert(s == ps.insert(e));  // extn
        assert(s.map(f).len() <= s.len());
    }
}

pub broadcast proof fn lemma_gset_len_empty<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> GSet::<A, FINITE>::empty() == s,
{
    if s.len() == 0 {
        broadcast use lemma_gset_remove_len;

        let a = s.choose();
        assert(!s.contains(a)) by {
            if s.contains(a) {
                assert(s.len() == s.remove(a).len() + 1);
            }
        }
        broadcast use lemma_gset_ext_equal;

        assert(s == GSet::<A, FINITE>::empty());
    }
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_gset_insert_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
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
        fold::lemma_fold_insert::<A, FINITE, nat>(s, 0, |b: nat, a: A| b + 1, a);
    }
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_gset_remove_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    broadcast use GSet::cast_finiteness_properties;

    lemma_gset_finite_from_type(s.to_finite().remove(a));
    lemma_congruence_extensionality(s, s.to_finite());
    s.to_finite().remove(a).congruent_infiniteness(s.remove(a));
    lemma_gset_insert_len(s.remove(a), a);
    if s.contains(a) {
        assert(s =~= s.remove(a).insert(a));
    } else {
        assert(s =~= s.remove(a));
    }
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_gset_contains_len<A>(s: GSet<A, Finite>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    let a = s.choose();
    assert(s.remove(a).insert(a) =~= s);
    lemma_gset_finite_from_type(s.remove(a));

    lemma_gset_insert_finite(s.remove(a), a);
    lemma_gset_insert_len(s.remove(a), a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_gset_choose_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    // Separate statements to work around https://github.com/verus-lang/verusfmt/issues/86
    broadcast use lemma_gset_contains_len;
    broadcast use lemma_gset_empty_len;
    broadcast use lemma_gset_ext_equal;
    broadcast use lemma_gset_insert_finite;
    broadcast use lemma_gset_insert_len;

    let pred = |s: GSet<A, FINITE>| s.finite() ==> s.len() == 0 <==> s =~= GSet::empty();
    fold::lemma_finite_set_induct(s, pred);
}

//////////////////////////////////////////////////////////////////////////////

} // verus!
