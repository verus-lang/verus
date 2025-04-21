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
pub struct Set<A, const Finite:bool = true> {
    set: spec_fn(A) -> bool,
}

pub type ISet<A> = Set<A, false>;

impl<A, const Finite:bool> Set<A, Finite> {
    // New is private because it can be used to construct infinite sets of either
    // type, and we need to exclude infinite predicates behind the finite version.
    //
    // TODO(jonh): can we enforce finiteness here without spreading it all over
    // the file? Proposed solution from Bryan: add a seq to the representation
    // that's used in the finite case.
    spec fn private_new(f: spec_fn(A) -> bool) -> Set<A, Finite> {
        Set {
            set: |a|
                if f(a) {
                    true
                } else {
                    false
                },
        }
    }

    // TODO(jonh): trusted because it calls private_new without proving that
    // mapped finite sets are finite. Waiting on provable finite=true repr.
    /// Returns the set contains an element `f(x)` for every element `x` in `self`.
    pub closed spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B, Finite> {
        Set::<B, Finite>::private_new(|a: B| exists|x: A| self.contains(x) && a == f(x))
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    /// Preserves finiteness of self.
    pub closed spec fn filter(self, f: spec_fn(A) -> bool) -> (out: Set<A, Finite>)
    {
        Set::private_new(|a| self.contains(a) && f(a))
    }
}

impl<A, const Finite: bool> Set<A, Finite> {
    pub closed spec fn to_finite(self) -> Set<A>
    {
        if self.finite() {
            Set{ set: self.set }
        } else {
            arbitrary()
        }
    }
}

/// Creates a finite set of integers in the range [lo, hi).
pub closed spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::private_new(|i: int| lo <= i && i < hi)
}

// TODO(jonh) broadcast
pub /*broadcast*/ proof fn lemma_set_int_range_ensures(lo: int, hi: int)
ensures
//     #[trigger(set_int_range(lo, hi))]
    forall |i: int| set_int_range(lo, hi).contains(i) <==> lo <= i && i < hi,
{
}

// TODO(jonh) broadcast
pub broadcast proof fn lemma_set_finite_from_type<A>(s: Set<A, true>)
ensures s.finite()
{
    // Preserving this is the reason for the trustedness in the
    // paragraph below. Until we replace the representation of finite
    // sets with seqs.
    admit();
}

impl<A> ISet<A> {
    pub closed spec fn new(f: spec_fn(A) -> bool) -> ISet<A> {
        Self::private_new(f)
    }
}

//////////////////////////////////////////////////////////////////////////////
// `private_new` should not appear below here.
// (I tried putting it inside an inner module with an inner type, but then all
// the definitions that need to talk about `set` get moved to that type, even
// though they're not involved in the trusted protection of Finite-ness. So
// absent another idea, this entire module is trusted to invoke private_new
// carefully to avoid violating the Finite=true => is_finite assumption.
//////////////////////////////////////////////////////////////////////////////

pub open spec fn congruent<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>) -> bool
{
    forall |a: A| s1.contains(a) <==> s2.contains(a)
}

// TODO(jonh): broadcast
pub proof fn congruent_len<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>)
requires
    congruent(s1, s2),
    s1.finite(),
ensures s1.len() == s2.len(),
decreases s1.len(),
{
    broadcast use lemma_set_empty_len;
    broadcast use lemma_set_len_empty;
    broadcast use lemma_set_remove_len;
    broadcast use lemma_set_choose_len;
    broadcast use lemma_set_ext_equal;
    broadcast use lemma_set_remove_finite;
    if s1 == Set::<A, Finite1>::empty() {
        assert( s1.len() == 0 );
        assert( forall |x| !s2.contains(x) );
        assert( s2 =~= Set::<A, Finite2>::empty() );    // trigger extn to get lemma_set_empty_len
        assert( s2.len() == 0 );
    } else {
        let x = s1.choose();
        assert( s1.finite() );
        assert( s1.len() != 0 );
        assert( s1.contains(x) );
        assert( s1.remove(x).len() + 1 == s1.len() );
        assert forall |a| s1.remove(x).contains(a) == s2.remove(x).contains(a) by {
            if a != x {
                assert( s1.remove(x).contains(a) == s1.contains(a) );
            }
        }
        assert( congruent(s1.remove(x), s2.remove(x)) );
        assert( s1.remove(x).finite() );
        congruent_len(s1.remove(x), s2.remove(x));
    }
}

pub proof fn congruent_infiniteness<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>)
requires congruent(s1, s2),
ensures s1.finite() <==> s2.finite(),
{
}

impl<A, const Finite:bool> Set<A, Finite> {
    pub open spec fn to_infinite(self) -> (infinite_out: ISet<A>)
    {
        ISet::new(|a| self.contains(a))
    }

    proof fn to_infinite_len(self)
    requires
        self.finite(),
    ensures
        self.len() == self.to_infinite().len(),
    decreases self.len()
    {
        broadcast use lemma_set_remove_len;
        broadcast use lemma_set_choose_finite;
        broadcast use lemma_set_choose_len;
        broadcast use lemma_set_empty_len;
        broadcast use lemma_set_len_empty;
        if self.len() == 0 {
            assert( self.to_infinite() =~= Set::empty() );
        } else {
            let a = self.choose();
            lemma_set_remove_finite(self, a);
            assert( self.to_infinite().remove(a) == self.remove(a).to_infinite() );
            self.remove(a).to_infinite_len();
        }
    }

    pub proof fn to_infinite_ensures(self)
    requires
        self.finite(),
    ensures
        forall |a: A| self.contains(a) <==> #[trigger] self.to_infinite().contains(a),
        self.len() == self.to_infinite().len(),
        self.to_infinite().finite(),
    {
        self.to_infinite_len()
    }

    /// The "empty" set.
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::empty"]
    pub closed spec fn empty() -> Set<A, Finite> {
        Set { set: |a| false }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::full"]
    pub open spec fn full() -> ISet<A> {
        ISet::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::contains"]
    pub closed spec fn contains(self, a: A) -> bool {
        (self.set)(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    /// Returns `true` if the first argument is a subset of the second.
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::subset_of"]
    pub open spec fn subset_of<const Finite2: bool>(self, s2: Set<A, Finite2>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le<const Finite2: bool>(self, s2: Set<A, Finite2>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::insert"]
    pub closed spec fn insert(self, a: A) -> Set<A, Finite> {
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
//     #[rustc_diagnostic_item = "verus::vstd::set::Set::remove"]
    pub closed spec fn remove(self, a: A) -> Set<A, Finite> {
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
    pub closed spec fn union<const Finite2: bool>(self, s2: Set<A, Finite2>) -> ISet<A> {
        Set { set: |a| (self.set)(a) || (s2.set)(a) }
    }

    /// Intersection of two sets.
    pub closed spec fn intersect<const Finite2: bool>(self, s2: Set<A, Finite2>) -> ISet<A> {
        Set { set: |a| (self.set)(a) && (s2.set)(a) }
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub closed spec fn difference<const Finite2: bool>(self, s2: Set<A, Finite2>) -> ISet<A> {
        Set { set: |a| (self.set)(a) && !(s2.set)(a) }
    }

    /// Set complement (within the space of all possible elements in `A`).
    pub closed spec fn complement(self) -> ISet<A> {
        Set { set: |a| !(self.set)(a) }
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
    pub open spec fn disjoint<const Finite2: bool>(self, s2: Set<A, Finite2>) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

impl<A> Set<A> {
    pub closed spec fn finite_union(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) || (s2.set)(a) }
    }

    /// If *either* set in an intersection is finite, the result is finite.
    /// To exploit that knowledge using this method, put the one you know is finite in the `self`
    /// position.
    pub closed spec fn finite_intersect<const Finite2: bool>(self, s2: Set<A, Finite2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && (s2.set)(a) }
    }

    pub closed spec fn finite_difference<const Finite2: bool>(self, s2: Set<A, Finite2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && !(s2.set)(a) }
    }
}

// TODO(jonh): proposal for discussion: spec_* functions preserve their type annotation, since
// that's probably how they'll most often be used.
impl<A> Set<A> {
    /// `+` operator, synonymous with `finite_union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.finite_union(s2)
    }

    /// `*` operator, synonymous with `finite_intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<const Finite2: bool>(self, s2: Set<A, Finite2>) -> Set<A> {
        self.finite_intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<const Finite2: bool>(self, s2: Set<A, Finite2>) -> Set<A> {
        self.finite_difference(s2)
    }

}

impl<A> ISet<A> {
    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: ISet<A>) -> ISet<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<const Finite2: bool>(self, s2: Set<A, Finite2>) -> ISet<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<const Finite2: bool>(self, s2: Set<A, Finite2>) -> ISet<A> {
        self.difference(s2)
    }

}

// Closures make triggering finicky but using this to trigger explicitly works well.
spec fn trigger_finite<A>(f: spec_fn(A) -> nat, ub: nat) -> bool {
    true
}

spec fn surj_on<A, const AFinite: bool, B>(f: spec_fn(A) -> B, s: Set<A, AFinite>) -> bool {
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
//         lemma_set_int_range_ensures,
        lemma_set_empty,
        lemma_set_new,
        lemma_set_insert_same,
        lemma_set_insert_different,
        lemma_set_remove_same,
        lemma_set_remove_insert,
        lemma_set_remove_different,
        lemma_set_union,
        lemma_set_finite_union,
        lemma_set_intersect,
        lemma_set_finite_intersect,
        lemma_set_difference,
        lemma_set_finite_difference,
        lemma_set_complement,
        lemma_set_ext_equal,
        lemma_set_ext_equal_deep,
        lemma_set_empty_finite,
        lemma_set_insert_finite,
        lemma_set_remove_finite,
    }

    pub open spec fn is_fun_commutative<A, B>(f: spec_fn(B, A) -> B) -> bool {
        forall|a1, a2, b| #[trigger] f(f(b, a2), a1) == f(f(b, a1), a2)
    }

    // This predicate is intended to be used like an inductive predicate, with the corresponding
    // introduction, elimination and induction rules proved below.
    #[verifier(opaque)]
    spec fn fold_graph<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A, Finite>, y: B, d: nat) -> bool
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
    proof fn lemma_fold_graph_empty_intro<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            fold_graph(z, f, Set::<A, Finite>::empty(), z, 0),
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_intro<A, const Finite: bool, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A, Finite>,
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
        assert( s.finite() ) by {
            if s == Set::<A, Finite>::empty() {
                let es = Set::<A>::empty();
                assert( congruent(es, s) );
                congruent_infiniteness(es, s);
                assert( s.finite() );
            } else {
                let es = s.to_finite();
                assert( congruent(s, es) );
                assert( congruent(s.remove(a), es.remove(a)) );
                assert( s.remove(a).finite() );
                assert( s.finite() );
            }
        }
        assert( s.remove(a).finite() ); // trigger?
//         assert( s.finite() );
//         set_finite_from_type(s);
//         lemma_set_insert_finite(s, a);
        assert( s.insert(a).finite() );
        assert( s.insert(a).remove(a).finite() );
//         assert(
//         {
//             let yr = y;
//             let s = s.insert(a);
//             let y = f(y, a);
//             let d = d + 1;
//                     &&& trigger_fold_graph(yr, a)
//                     &&& d > 0
//                     &&& s.remove(a).finite()
//                     &&& s.contains(a)
//                     &&& fold_graph(z, f, s.remove(a), yr, sub(d, 1))
//                     &&& y == f(yr, a)
//         }
//         );
//         assert( fold_graph(z, f, s.insert(a), f(y, a), d + 1) );
    }

    // Elimination rules
    proof fn lemma_fold_graph_empty_elim<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B, y: B, d: nat)
        requires
            fold_graph(z, f, Set::<A, Finite>::empty(), y, d),
        ensures
            z == y,
            d == 0,
    {
        reveal(fold_graph);
    }

    proof fn lemma_fold_graph_insert_elim<A, const Finite: bool, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A, Finite>,
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

    proof fn lemma_fold_graph_insert_elim_aux<A, const Finite: bool, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A, Finite>,
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
    proof fn lemma_fold_graph_induct<A, const Finite: bool, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A, Finite>,
        y: B,
        d: nat,
        pred: spec_fn(Set<A, Finite>, B, nat) -> bool,
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
            lemma_fold_graph_empty_elim::<A, Finite, B>(z, f, y, d);
        } else {
            let a = s.choose();
            lemma_fold_graph_insert_elim(z, f, s.remove(a), y, d, a);
            let yp = choose|yp|
                y == f(yp, a) && #[trigger] fold_graph(z, f, s.remove(a), yp, sub(d, 1));
            assert( pred(Set::empty(), z, 0) ); // flaky trigger failure?
            lemma_fold_graph_induct::<A, Finite, B>(z, f, s.remove(a), yp, sub(d, 1), pred);
        }
    }

    impl<A, const Finite: bool> Set<A, Finite> {
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

    proof fn lemma_fold_graph_finite<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A, Finite>, y: B, d: nat)
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.finite(),
    {
        broadcast use group_set_axioms_early;

        let pred = |s: Set<A, Finite>, y, d| s.finite();

        let empty = Set::<A, Finite>::empty();
        lemma_set_finite_from_type(empty.to_finite());
        congruent_infiniteness(empty, empty.to_finite());

        lemma_fold_graph_induct::<A, Finite, B>(z, f, s, y, d, pred);
    }

    proof fn lemma_fold_graph_deterministic<A, const Finite: bool, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: Set<A, Finite>,
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
        let pred = |s: Set<A, Finite>, y1: B, d1: nat|
            forall|y2, d2| fold_graph(z, f, s, y2, d2) ==> y1 == y2 && d2 == d1;
        // Base case
        assert(pred(Set::empty(), z, 0)) by {
            assert forall|y2, d2| fold_graph(z, f, Set::<A, Finite>::empty(), y2, d2) implies z == y2 && d2
                == 0 by {
                lemma_fold_graph_empty_elim::<A, Finite, B>(z, f, y2, d2);
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
        lemma_fold_graph_induct::<A, Finite, B>(z, f, s, y2, d2, pred);
    }

    proof fn lemma_fold_is_fold_graph<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A, Finite>, y: B, d: nat)
        requires
            is_fun_commutative(f),
            fold_graph(z, f, s, y, d),
        ensures
            s.fold(z, f) == y,
    {
        lemma_fold_graph_finite::<A, Finite, B>(z, f, s, y, d);
        if s.fold(z, f) != y {
            let (y2, d2) = choose|y2, d2| fold_graph(z, f, s, y2, d2) && y2 != y;
            lemma_fold_graph_deterministic::<A, Finite, B>(z, f, s, y2, y, d2, d);
            assert(false);
        }
    }

    // At this point set cardinality is not yet defined, so we can't easily give a decreasing
    // measure to prove the subsequent lemma `lemma_fold_graph_exists`. Instead, we first prove
    // this lemma, for which we use the upper bound of a finiteness witness as the decreasing
    // measure.
    pub proof fn lemma_finite_set_induct<A, const Finite: bool>(s: Set<A, Finite>, pred: spec_fn(Set<A, Finite>) -> bool)
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

    proof fn lemma_finite_set_induct_aux<A, const Finite: bool>(
        s: Set<A, Finite>,
        f: spec_fn(A) -> nat,
        ub: nat,
        pred: spec_fn(Set<A, Finite>) -> bool,
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

    proof fn lemma_fold_graph_exists<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B, s: Set<A, Finite>)
        requires
            s.finite(),
            is_fun_commutative(f),
        ensures
            exists|y, d| fold_graph(z, f, s, y, d),
    {
        let pred = |s| exists|y, d| fold_graph(z, f, s, y, d);
        // Base case
        assert(fold_graph(z, f, Set::<A, Finite>::empty(), z, 0)) by {
            lemma_fold_graph_empty_intro::<A, Finite, B>(z, f);
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

    pub broadcast proof fn lemma_fold_insert<A, const Finite: bool, B>(s: Set<A, Finite>, z: B, f: spec_fn(B, A) -> B, a: A)
        requires
            s.finite(),
            !s.contains(a),
            is_fun_commutative(f),
        ensures
            #[trigger] s.insert(a).fold(z, f) == f(s.fold(z, f), a),
    {
        lemma_fold_graph_exists::<A, Finite, B>(z, f, s);
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, s, y, d);
        lemma_fold_graph_insert_intro(z, f, s, s.fold(z, f), d, a);
        lemma_fold_is_fold_graph::<A, Finite, B>(z, f, s.insert(a), f(s.fold(z, f), a), d + 1);
    }

    pub broadcast proof fn lemma_fold_empty<A, const Finite: bool, B>(z: B, f: spec_fn(B, A) -> B)
        ensures
            #[trigger] Set::<A, Finite>::empty().fold(z, f) == z,
    {
        let (y, d): (B, nat) = choose|y, d| fold_graph(z, f, Set::<A, Finite>::empty(), y, d);
        lemma_fold_graph_empty_intro::<A, Finite, B>(z, f);
        lemma_fold_graph_empty_elim::<A, Finite, B>(z, f, y, d);
    }

}

/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A, const Finite: bool>(a: A)
    ensures
        !(#[trigger] Set::<A, Finite>::empty().contains(a)),
{
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
pub broadcast proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] Set::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A, const Finite: bool>(s: Set<A, Finite>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_set_remove_insert<A, const Finite: bool>(s: Set<A, Finite>, a: A)
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
pub broadcast proof fn lemma_set_remove_different<A, const Finite: bool>(s: Set<A, Finite>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A, const Finite: bool, const Finite2: bool>(s1: Set<A, Finite>, s2: Set<A, Finite2>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The finite-typed union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_finite_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.finite_union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A, const Finite: bool, const Finite2: bool>(s1: Set<A, Finite>, s2: Set<A, Finite2>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The finite-typed intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_finite_intersect<A, const Finite2: bool>(s1: Set<A>, s2: Set<A, Finite2>, a: A)
    ensures
        #[trigger] s1.finite_intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The finite-typed set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_finite_difference<A, const Finite2: bool>(s1: Set<A>, s2: Set<A, Finite2>, a: A)
    ensures
        #[trigger] s1.finite_difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_set_complement<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn lemma_set_ext_equal<A, const Finite: bool>(s1: Set<A, Finite>, s2: Set<A, Finite>)
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

pub broadcast proof fn lemma_set_ext_equal_deep<A, const Finite: bool>(s1: Set<A, Finite>, s2: Set<A, Finite>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

// TODO(jonh): restore these once we're integrated with map again.
// Also, why is mk_map a set method? Should be a map method! Tangly.
// pub broadcast proof fn lemma_mk_map_domain<K, V>(s: ISet<K>, f: spec_fn(K) -> V)
//     ensures
//         #[trigger] s.mk_map(f).dom() == s,
// {
//     admit();
// }
// 
// pub broadcast proof fn lemma_mk_map_index<K, V>(s: ISet<K>, f: spec_fn(K) -> V, key: K)
//     requires
//         s.contains(key),
//     ensures
//         #[trigger] s.mk_map(f)[key] == f(key),
// {
//     admit();
// }

// Trusted axioms about finite
/// The empty set is finite.
pub broadcast proof fn lemma_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
pub broadcast proof fn lemma_set_insert_finite<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    lemma_set_finite_from_type(s.to_finite().insert(a));
    congruent_infiniteness(s.to_finite().insert(a), s.insert(a));
}

pub broadcast proof fn lemma_set_remove_finite<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    lemma_set_finite_from_type(s.to_finite().remove(a));
    congruent_infiniteness(s.to_finite().remove(a), s.remove(a));
}

/// The result of removing an element `a` from a finite set `s` is also finite.
// pub broadcast proof fn lemma_set_remove_finite<A>(s: Set<A>, a: A)
//     requires
//         s.finite(),
//     ensures
//         #[trigger] s.remove(a).finite(),
// {
//     let (f, ub) = choose|f: spec_fn(A) -> nat, ub: nat| #[trigger]
//         trigger_finite(f, ub) && surj_on(f, s) && (forall|a| s.contains(a) ==> f(a) < ub);
//     assert forall|a1, a2|
//         #![all_triggers]
//         s.remove(a).contains(a1) && s.remove(a).contains(a2) && a1 != a2 implies f(a1) != f(a2) by {
//         if a != a1 {
//             assert(s.contains(a1));
//         }
//         if a != a2 {
//             assert(s.contains(a2));
//         }
//     };
//     assert(surj_on(f, s.remove(a)));
//     assert forall|a2| s.remove(a).contains(a2) implies #[trigger] f(a2) < ub by {
//         if a == a2 {
//         } else {
//             assert(s.contains(a2));
//         }
//     };
// }

/// The union of two finite sets is finite.
pub broadcast proof fn lemma_set_union_finite<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>)
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
pub broadcast proof fn lemma_set_intersect_finite<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>)
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
pub broadcast proof fn lemma_set_difference_finite<A, const Finite1: bool, const Finite2: bool>(s1: Set<A, Finite1>, s2: Set<A, Finite2>)
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
// TODO(jonh): rename choose_infinite!
pub broadcast proof fn lemma_set_choose_finite<A, const Finite: bool>(s: Set<A, Finite>)
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
// The following, with lemma_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A, const Finite: bool>()
    ensures
        #[trigger] Set::<A, Finite>::empty().len() == 0,
{
    fold::lemma_fold_empty::<A, Finite, nat>(0, |b: nat, a: A| b + 1);
}

pub broadcast proof fn lemma_set_len_empty<A, const Finite: bool>(s: Set<A, Finite>)
requires s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> Set::<A, Finite>::empty() == s,
{
    if s.len() == 0 {
        broadcast use lemma_set_remove_len;
        let a = s.choose();
        assert( !s.contains(a) ) by {
            if s.contains(a) {
                assert( s.len() == s.remove(a).len() + 1 );
            }
        }
        broadcast use lemma_set_ext_equal;
        assert( s == Set::<A, Finite>::empty() );
    }
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A, const Finite: bool>(s: Set<A, Finite>, a: A)
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
        fold::lemma_fold_insert::<A, Finite, nat>(s, 0, |b: nat, a: A| b + 1, a);
    }
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_remove_len<A, const Finite: bool>(s: Set<A, Finite>, a: A)
    requires
        s.finite()
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    lemma_set_finite_from_type(s.to_finite().remove(a));
    congruent_infiniteness(s.to_finite().remove(a), s.remove(a));
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
//     lemma_set_remove_finite(s, a);   // TODO delete; obvious from types now
//
    lemma_set_finite_from_type(s.remove(a));

    lemma_set_insert_finite(s.remove(a), a);
    lemma_set_insert_len(s.remove(a), a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A, const Finite: bool>(s: Set<A, Finite>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    // Separate statements to work around https://github.com/verus-lang/verusfmt/issues/86
    broadcast use lemma_set_contains_len;
    broadcast use lemma_set_empty_len;
    broadcast use lemma_set_ext_equal;
    broadcast use lemma_set_insert_finite;
    broadcast use lemma_set_insert_len;

    let pred = |s: Set<A, Finite>| s.finite() ==> s.len() == 0 <==> s =~= Set::empty();
    fold::lemma_finite_set_induct(s, pred);
}

// filter definition is closed now, so we expose its meaning through this lemma
pub broadcast proof fn lemma_set_filter_is_intersect<A, const Finite: bool>(s: Set<A, Finite>, f: spec_fn(A) -> bool)
ensures
    congruent(#[trigger] s.filter(f), s.intersect(ISet::new(f)))
{
}

pub broadcast group group_set_axioms {
//         lemma_set_int_range_ensures,
    lemma_set_finite_from_type,
    lemma_set_empty,
    lemma_set_new,
    lemma_set_insert_same,
    lemma_set_insert_different,
    lemma_set_remove_same,
    lemma_set_remove_insert,
    lemma_set_remove_different,
    lemma_set_union,
    lemma_set_finite_union,
    lemma_set_intersect,
    lemma_set_finite_intersect,
    lemma_set_difference,
    lemma_set_finite_difference,
    lemma_set_complement,
    lemma_set_ext_equal,
    lemma_set_ext_equal_deep,
//     lemma_mk_map_domain,
//     lemma_mk_map_index,
    lemma_set_empty_finite,
    lemma_set_insert_finite,
    lemma_set_remove_finite,
    lemma_set_union_finite,
    lemma_set_intersect_finite,
    lemma_set_difference_finite,
    lemma_set_choose_finite,
    lemma_set_empty_len,
    lemma_set_len_empty,
    lemma_set_insert_len,
    lemma_set_remove_len,
    lemma_set_contains_len,
    lemma_set_choose_len,
    lemma_set_filter_is_intersect,
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! xset_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::xset::Set::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! xset {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::xset::xset_internal!($($tail)*))
    };
}

pub use xset_internal;
pub use xset;

} // verus!
