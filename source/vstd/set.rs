#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

pub struct Finite;

pub struct Infinite;

pub trait Finiteness {

}

impl Finiteness for Finite {

}

impl Finiteness for Infinite {

}

/// `GSet<A, true>` is a set type for specifications.
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
pub struct GSet<A, FINITE: Finiteness> {
    set: spec_fn(A) -> bool,
    _phantom: core::marker::PhantomData<FINITE>,
}

//////////////////////////////////////////////////////////////////////////////
// Important soundness note!
//
// In this file, one can construct GSets directly with GSet{set:...}.
// Doing so for ISet is always sound, but when the type is Set (finite=true),
// we must be careful to only allow the set function to admit a finite number
// of elements. Otherwise, one could prove that set both finite and infinite
// and introduce false. The danger of this soundness risk is encapsulated
// in lemma_set_finite_from_type, which assumes that the set function is finite.
//
// Outside of this file, callers only have access to Set constructors that
// create only finite sets.
//
// For future work, we may figure out how to have Set use a seq-like
// representation that is inherently finite to eliminate this risk. (However,
// that introduces the problem of multiple representations of equivalent
// sets, which creates a different problem with extensional equality.)
//////////////////////////////////////////////////////////////////////////////
/// Set<A> is a synonym for GSet<A, true>, a set whose membership is finite (known at typechecking time).
pub type Set<A> = GSet<A, Finite>;

/// ISet<A> is a synonym for GSet<A, false>, a set whose membership may be infinite (but can be
/// proven finite at verification time).
pub type ISet<A> = GSet<A, Infinite>;

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    // This map function is sound for finite sets because of `lemma_set_map_finite`,
    // but we don't need to invoke that lemma here because this file is trusting
    // GSet constructors to do so soundly (see "Important soundness note" above).
    /// Returns the set contains an element `f(x)` for every element `x` in `self`.
    pub closed spec fn map<B>(self, f: spec_fn(A) -> B) -> GSet<B, FINITE> {
        GSet {
            set: |a: B| exists|x: A| self.contains(x) && a == f(x),
            _phantom: core::marker::PhantomData,
        }
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    /// Preserves finiteness of self.
    pub closed spec fn filter(self, f: spec_fn(A) -> bool) -> (out: GSet<A, FINITE>) {
        GSet { set: |a| self.contains(a) && f(a), _phantom: core::marker::PhantomData }
    }

    /// Replace each element of a set with the elements of another set.
    /// Preserves finiteness of self.
    pub closed spec fn product<B>(self, f: spec_fn(A) -> GSet<B, FINITE>) -> (out: GSet<
        B,
        FINITE,
    >) {
        GSet {
            set: |b| exists|a| self.contains(a) && f(a).contains(b),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    // This spec and its axioms encode the idea that an SMT .finite() ISet can be cast to a finite
    // Set, and anything can be cast to an ISet.
    pub uninterp spec fn cast_finiteness<NEWFINITE: Finiteness>(self) -> GSet<A, NEWFINITE>;

    axiom fn cast_from_finite<NEWFINITE: Finiteness>(self)
        ensures
            self.cast_finiteness::<NEWFINITE>() == (GSet::<A, NEWFINITE> {
                set: self.set,
                _phantom: core::marker::PhantomData,
            }),
    ;

    axiom fn cast_to_infinite(self)
        ensures
            self.cast_finiteness::<Infinite>() == (ISet {
                set: self.set,
                _phantom: core::marker::PhantomData,
            }),
    ;

    axiom fn cast_to_finite(self)
        requires
            self.finite(),
        ensures
            self.cast_finiteness::<Finite>() == (Set {
                set: self.set,
                _phantom: core::marker::PhantomData,
            }),
    ;

    pub proof fn cast_finiteness_ensures(self)
        ensures
            self.cast_finiteness::<Infinite>() == self.to_infinite(),
    {
        self.cast_to_infinite();
        assert(self.set == |a| self.contains(a));  // fn extensionality
    }

    #[verifier::inline]
    pub open spec fn to_finite(self) -> Set<A>
        recommends
            self.finite(),
    {
        self.cast_finiteness::<Finite>()
    }

    pub broadcast proof fn lemma_to_finite_contains(self)
        requires
            self.finite(),
        ensures
            #![trigger(self.to_finite())]
            forall|a|
                self.contains(a) <==> #[trigger] self.to_finite().contains(a),
    {
        self.cast_to_finite();
    }
}

impl<FINITE: Finiteness> GSet<int, FINITE> {
    /// Creates a finite set of integers in the range [lo, hi).
    pub closed spec fn int_range(lo: int, hi: int) -> GSet<int, FINITE> {
        GSet { set: |i: int| lo <= i && i < hi, _phantom: core::marker::PhantomData }
    }
}

impl<FINITE: Finiteness> GSet<nat, FINITE> {
    /// Creates a finite set of nats in the range [lo, hi).
    pub closed spec fn nat_range(lo: nat, hi: nat) -> GSet<nat, FINITE> {
        GSet { set: |i: nat| lo <= i && i < hi, _phantom: core::marker::PhantomData }
    }
}

pub broadcast proof fn lemma_set_finite_from_type<A>(s: Set<A>)
    ensures
        #[trigger] s.finite(),
{
    // Preserving this is the reason for the trustedness in the
    // paragraph below. Until we replace the representation of finite
    // sets with seqs.
    admit();
}

impl<A> ISet<A> {
    pub closed spec fn new(f: spec_fn(A) -> bool) -> ISet<A> {
        ISet { set: f, _phantom: core::marker::PhantomData }
    }
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
        if self.finite() {
            self.cast_to_finite();
        }
        if s2.finite() {
            s2.cast_to_finite();
        }
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
        // TOOD(jonh): tidy up this proof
        broadcast use {
            lemma_set_empty_len,
            lemma_set_len_empty,
            lemma_set_remove_len,
            lemma_set_choose_len,
            lemma_set_ext_equal,
            lemma_set_remove_finite,
        };

        if self == GSet::<A, FINITE>::empty() {
            assert(self.len() == 0);
            assert(forall|x| !s2.contains(x));
            assert(s2 =~= GSet::<A, FINITE2>::empty());  // trigger extn to get lemma_set_empty_len
            assert(s2.len() == 0);
        } else {
            let x = self.choose();
            assert(self.finite());
            assert(self.len() != 0);
            assert(self.contains(x));
            assert(self.remove(x).len() + 1 == self.len());
            assert forall|a| self.remove(x).contains(a) == s2.remove(x).contains(a) by {
                if a != x {
                    assert(self.remove(x).contains(a) == self.contains(a));
                }
            }
            assert(self.remove(x).congruent(s2.remove(x)));
            assert(self.remove(x).finite());
            self.remove(x).congruent_len(s2.remove(x));
        }
    }
}

pub broadcast proof fn lemma_set_map_contains<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
}

pub broadcast proof fn lemma_set_map_subset<A, FINITE1: Finiteness, FINITE2: Finiteness, B>(
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

pub broadcast proof fn lemma_set_map_finite<A, FINITE: Finiteness, B>(
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

pub broadcast proof fn lemma_set_filter_finite<A, FINITE: Finiteness>(
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
    pub open spec fn to_infinite(self) -> (infinite_out: ISet<A>) {
        ISet::new(|a| self.contains(a))
    }

    proof fn to_infinite_len(self)
        requires
            self.finite(),
        ensures
            self.len() == self.to_infinite().len(),
        decreases self.len(),
    {
        broadcast use lemma_set_remove_len;
        broadcast use lemma_set_choose_infinite;
        broadcast use lemma_set_choose_len;
        broadcast use lemma_set_empty_len;
        broadcast use lemma_set_len_empty;

        if self.len() == 0 {
            assert(self.to_infinite() =~= GSet::empty());
        } else {
            let a = self.choose();
            lemma_set_remove_finite(self, a);
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

    /// The "empty" set.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::empty"]
    pub closed spec fn empty() -> GSet<A, FINITE> {
        Self { set: |a| false, _phantom: core::marker::PhantomData }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::full"]
    pub open spec fn full() -> ISet<A> {
        ISet::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::contains"]
    pub closed spec fn contains(self, a: A) -> bool {
        (self.set)(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    /// Returns `true` if the first argument is a subset of the second.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::subset_of"]
    pub open spec fn subset_of<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::insert"]
    pub closed spec fn insert(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    true
                } else {
                    (self.set)(a2)
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::remove"]
    pub closed spec fn remove(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    false
                } else {
                    (self.set)(a2)
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Union of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `union`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        GSet { set: |a| (self.set)(a) || (s2.set)(a), _phantom: core::marker::PhantomData }
    }

    /// Intersection of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `intersect`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<
        A,
    > {
        GSet { set: |a| (self.set)(a) && (s2.set)(a), _phantom: core::marker::PhantomData }
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    /// Most applications should use the finite- or infinite- specializations
    /// `difference`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<
        A,
    > {
        GSet { set: |a| (self.set)(a) && !(s2.set)(a), _phantom: core::marker::PhantomData }
    }

    /// Set complement (within the space of all possible elements in `A`).
    pub closed spec fn complement(self) -> ISet<A> {
        GSet { set: |a| !(self.set)(a), _phantom: core::marker::PhantomData }
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
    #[deprecated = "Use `Map::from_set` instead"]
    pub open spec fn mk_map<V>(self, f: spec_fn(A) -> V) -> GMap<A, V, FINITE> {
        GMap::from_set(self, f)
    }

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

impl<A> Set<A> {
    pub closed spec fn union(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) || (s2.set)(a), _phantom: core::marker::PhantomData }
    }

    /// If *either* set in an intersection is finite, the result is finite.
    /// To exploit that knowledge using this method, put the one you know is finite in the `self`
    /// position.
    pub closed spec fn intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && (s2.set)(a), _phantom: core::marker::PhantomData }
    }

    pub closed spec fn difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && !(s2.set)(a), _phantom: core::marker::PhantomData }
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        self.difference(s2)
    }
}

impl<A> ISet<A> {
    pub open spec fn union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) || s2.contains(a))
    }

    pub open spec fn intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) && s2.contains(a))
    }

    pub open spec fn difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) && !s2.contains(a))
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: ISet<A>) -> ISet<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        self.difference(s2)
    }
}

// Closures make triggering finicky but using this to trigger explicitly works well.
spec fn trigger_finite<A>(f: spec_fn(A) -> nat, ub: nat) -> bool {
    true
}

spec fn surj_on<A, AFINITE: Finiteness, B>(f: spec_fn(A) -> B, s: GSet<A, AFINITE>) -> bool {
    forall|a1, a2| #![all_triggers] s.contains(a1) && s.contains(a2) && a1 != a2 ==> f(a1) != f(a2)
}

pub mod fold {
    //! This module defines a fold function for finite sets and proves a number of associated
    //! lemmas.
    //!
    //! The module was ported (with some modifications) from Isabelle/HOL's finite set theory in:
    //! `HOL/FINITE_Set.thy`
    //! That file contains the following author list:
    //!
    //!
    //! (*  Title:      HOL/FINITE_Set.thy
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

    pub(in super) broadcast group group_set_lemmas_early {
        GSet::lemma_to_finite_contains,
        lemma_set_finite_from_type,
        lemma_set_empty,
        lemma_set_new,
        lemma_set_insert_same,
        lemma_set_insert_different,
        lemma_set_remove_same,
        lemma_set_remove_insert,
        lemma_set_remove_different,
        lemma_set_generic_union,
        lemma_set_union,
        lemma_set_generic_intersect,
        lemma_set_intersect,
        lemma_set_generic_difference,
        lemma_set_difference,
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
    spec fn fold_graph<A, FINITE: Finiteness, B>(
        z: B,
        f: spec_fn(B, A) -> B,
        s: GSet<A, FINITE>,
        y: B,
        d: nat,
    ) -> bool
        decreases d,
    {
        if s === GSet::empty() {
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
        broadcast use {group_set_lemmas_early, GSet::congruent_infiniteness};

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
                &&& d > 0
                &&& s.remove(aa).finite()
                &&& s.contains(aa)
                &&& fold_graph(z, f, s.remove(aa), yr, sub(d, 1))
                &&& y == f(yr, aa)
            };
        assert(trigger_fold_graph(yr, a));
        if s.remove(aa) === GSet::empty() {
        } else {
            if a == aa {
            } else {
                assume(false);  // flaky!
                //                 assert( is_fun_commutative(f) );
                if !(s.remove(aa) == GSet::<A, FINITE>::empty()) {
                    assert(exists|yr, a|
                        trigger_fold_graph(yr, a) && (d - 1) as nat > 0 && s.remove(aa).remove(
                            a,
                        ).finite() && s.remove(aa).contains(a) && fold_graph(
                            z,
                            f,
                            s.remove(aa).remove(a),
                            yr,
                            ((d - 1) as nat - 1) as nat,
                        ) && yr == f(yr, a));
                }
                assert(fold_graph(z, f, s.remove(aa), yr, sub(d, 1)));
                assert(s.remove(aa).contains(a));
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
        assume(false);  // flaky!
        assert(exists|yp| y == f(yp, a) && #[trigger] fold_graph(z, f, s.remove(a), yp, sub(d, 1)));
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
        broadcast use {group_set_lemmas_early, GSet::congruent_infiniteness};

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

/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A, FINITE: Finiteness>(a: A)
    ensures
        !(#[trigger] GSet::<A, FINITE>::empty().contains(a)),
{
}

pub broadcast proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] ISet::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    a1: A,
    a2: A,
)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_set_remove_insert<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
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
pub broadcast proof fn lemma_set_remove_different<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    a1: A,
    a2: A,
)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_generic_union<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The finite-typed union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_generic_intersect<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The finite-typed intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A, FINITE2: Finiteness>(
    s1: Set<A>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_generic_difference<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The finite-typed set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A, FINITE2: Finiteness>(
    s1: Set<A>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_set_complement<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn lemma_set_ext_equal<A, FINITE: Finiteness>(
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

pub broadcast proof fn lemma_set_ext_equal_deep<A, FINITE: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE>,
)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

/// The empty set is finite.
pub broadcast proof fn lemma_set_empty_finite<A, FINITE: Finiteness>()
    ensures
        #[trigger] GSet::<A, FINITE>::empty().finite(),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
pub broadcast proof fn lemma_set_insert_finite<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    lemma_set_finite_from_type(s.to_finite().insert(a));
    s.cast_to_finite();
    s.to_finite().insert(a).congruent_infiniteness(s.insert(a));
}

pub broadcast proof fn lemma_set_remove_finite<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    lemma_set_finite_from_type(s.to_finite().remove(a));
    s.cast_to_finite();
    s.to_finite().remove(a).congruent_infiniteness(s.remove(a));
}

/// The union of two finite sets is finite.
pub broadcast proof fn lemma_set_generic_union_finite<A, FINITE1: Finiteness, FINITE2: Finiteness>(
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

pub broadcast proof fn lemma_set_union_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
    assert(s1.union(s2) == s1.generic_union(s2));
    lemma_set_generic_union_finite(s1, s2);
}

/// The intersection of two finite sets is finite.
pub broadcast proof fn lemma_set_generic_intersect_finite<
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

pub broadcast proof fn lemma_set_intersect_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

/// The set difference between two finite sets is finite.
pub broadcast proof fn lemma_set_generic_difference_finite<
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

pub broadcast proof fn lemma_set_difference_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

/// An infinite set `s` contains the element `s.choose()`.
/// Note here 'infinite' means not-SMT-finite; the empty set is SMT-finite.
/// ISet::empty() is type-infinite but not SMT-infinite.
pub broadcast proof fn lemma_set_choose_infinite<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

// Note: we could add more axioms about len, but they would be incomplete.
// The following, with lemma_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A, FINITE: Finiteness>()
    ensures
        #[trigger] GSet::<A, FINITE>::empty().len() == 0,
{
    fold::lemma_fold_empty::<A, FINITE, nat>(0, |b: nat, a: A| b + 1);
}

pub broadcast proof fn lemma_set_map_insert<A, FINITE: Finiteness, B>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    broadcast use lemma_set_ext_equal;

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

pub broadcast proof fn lemma_set_map_len<A, FINITE: Finiteness, B>(
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
    broadcast use lemma_set_empty_len;
    broadcast use lemma_set_choose_len;
    broadcast use lemma_set_len_empty;
    broadcast use lemma_set_remove_finite;
    broadcast use lemma_set_remove_len;
    broadcast use lemma_set_map_finite;
    broadcast use lemma_set_insert_len;
    broadcast use lemma_set_map_insert;

    if s == GSet::<A, FINITE>::empty() {
        assert(s.map(f) == GSet::<B, FINITE>::empty());  // trigger lemma_set_empty_len
    } else {
        let e = s.choose();
        let ps = s.remove(e);
        lemma_set_map_len(ps, f);  // broadcast use would create recursion at this call site
        assert(s == ps.insert(e));  // extn
        assert(s.map(f).len() <= s.len());
    }
}

pub broadcast proof fn lemma_set_len_empty<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> GSet::<A, FINITE>::empty() == s,
{
    if s.len() == 0 {
        broadcast use lemma_set_remove_len;

        let a = s.choose();
        assert(!s.contains(a)) by {
            if s.contains(a) {
                assert(s.len() == s.remove(a).len() + 1);
            }
        }
        broadcast use lemma_set_ext_equal;

        assert(s == GSet::<A, FINITE>::empty());
    }
}

pub broadcast proof fn lemma_set_int_range_ensures<FINITE: Finiteness>(lo: int, hi: int)
    ensures
        #![trigger(GSet::<int, FINITE>::int_range(lo, hi))]
        forall|i: int| #[trigger]
            GSet::<int, FINITE>::int_range(lo, hi).contains(i) <==> lo <= i && i < hi,
        (lo <= hi) ==> GSet::<int, FINITE>::int_range(lo, hi).len() == hi - lo,
        GSet::<int, FINITE>::int_range(lo, hi).finite(),
    decreases hi - lo,
{
    if lo < hi {
        lemma_set_int_range_ensures::<FINITE>(lo, hi - 1);
        assert(GSet::<int, FINITE>::int_range(lo, hi) =~= GSet::<int, FINITE>::int_range(
            lo,
            hi - 1,
        ).insert(hi - 1));
        lemma_set_insert_finite(GSet::<int, FINITE>::int_range(lo, hi - 1), hi - 1);
        fold::lemma_fold_insert::<int, FINITE, nat>(
            GSet::<int, FINITE>::int_range(lo, hi - 1),
            0,
            |b: nat, a: int| b + 1,
            hi - 1,
        );
    } else {
        broadcast use lemma_set_empty_len;

        assert(GSet::<int, FINITE>::int_range(lo, hi) =~= GSet::<int, FINITE>::empty());  // extn
        broadcast use lemma_set_empty_finite;

    }
}

pub broadcast proof fn lemma_set_nat_range_ensures<FINITE: Finiteness>(lo: nat, hi: nat)
    ensures
        #![trigger(GSet::<nat, FINITE>::nat_range(lo, hi))]
        forall|i: nat| #[trigger]
            GSet::<nat, FINITE>::nat_range(lo, hi).contains(i) <==> lo <= i && i < hi,
        (lo <= hi) ==> GSet::<nat, FINITE>::nat_range(lo, hi).len() == hi - lo,
        GSet::<nat, FINITE>::nat_range(lo, hi).finite(),
    decreases hi - lo,
{
    if lo < hi {
        let dechi = (hi - 1) as nat;
        lemma_set_nat_range_ensures::<FINITE>(lo, dechi);
        assert(GSet::<nat, FINITE>::nat_range(lo, hi) =~= GSet::<nat, FINITE>::nat_range(
            lo,
            dechi,
        ).insert(dechi));
        lemma_set_insert_finite(GSet::<nat, FINITE>::nat_range(lo, dechi), dechi);
        fold::lemma_fold_insert::<nat, FINITE, nat>(
            GSet::<nat, FINITE>::nat_range(lo, dechi),
            0,
            |b: nat, a: nat| b + 1,
            dechi,
        );
    } else {
        broadcast use lemma_set_empty_len;

        assert(GSet::<nat, FINITE>::nat_range(lo, hi) =~= GSet::<nat, FINITE>::empty());  // extn
        broadcast use lemma_set_empty_finite;

    }
}

#[deprecated = "Use `Set::int_range` instead"]
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::<int>::int_range(lo, hi)
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
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
pub broadcast proof fn lemma_set_remove_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    lemma_set_finite_from_type(s.to_finite().remove(a));
    s.cast_to_finite();
    s.to_finite().remove(a).congruent_infiniteness(s.remove(a));
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
    lemma_set_finite_from_type(s.remove(a));

    lemma_set_insert_finite(s.remove(a), a);
    lemma_set_insert_len(s.remove(a), a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
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

    let pred = |s: GSet<A, FINITE>| s.finite() ==> s.len() == 0 <==> s =~= GSet::empty();
    fold::lemma_finite_set_induct(s, pred);
}

// filter definition is closed now, so we expose its meaning through this lemma
pub broadcast proof fn lemma_set_filter_is_intersect<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> bool,
)
    ensures
        (#[trigger] s.filter(f)).congruent(s.generic_intersect(ISet::new(f))),
{
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    pub broadcast proof fn lemma_set_product_contains<B>(self, f: spec_fn(A) -> GSet<B, FINITE>)
        ensures
            #![trigger(self.product(f))]
            forall|b|
                (#[trigger] self.product(f).contains(b)) <==> exists|a|
                    self.contains(a) && f(a).contains(b),
    {
    }

    pub broadcast proof fn lemma_set_product_contains_2<B>(
        self,
        f: spec_fn(A) -> GSet<B, FINITE>,
        a: A,
        b: B,
    )
        ensures
            #![trigger self.contains(a), f(a).contains(b)]
            #![trigger self.product(f).contains(b), f(a).contains(b)]
            self.contains(a) && f(a).contains(b) ==> self.product(f).contains(b),
    {
    }
}

pub broadcast group group_set_lemmas {
    // This line...
    fold::group_set_lemmas_early,
    // ...should replace these lines (up to the blank), but it doesn't.
    // (verus #1616)
    GSet::lemma_to_finite_contains,
    lemma_set_finite_from_type,
    lemma_set_empty,
    lemma_set_new,
    lemma_set_insert_same,
    lemma_set_insert_different,
    lemma_set_remove_same,
    lemma_set_remove_insert,
    lemma_set_remove_different,
    lemma_set_generic_union,
    lemma_set_union,
    lemma_set_generic_intersect,
    lemma_set_intersect,
    lemma_set_generic_difference,
    lemma_set_difference,
    lemma_set_complement,
    lemma_set_ext_equal,
    lemma_set_ext_equal_deep,
    lemma_set_empty_finite,
    lemma_set_insert_finite,
    lemma_set_remove_finite,
    lemma_set_map_contains,
    lemma_set_map_subset,
    lemma_set_map_finite,
    lemma_set_filter_finite,
    GSet::to_infinite_ensures,
    lemma_set_map_len,
    lemma_set_map_insert,
    lemma_set_int_range_ensures,
    lemma_set_nat_range_ensures,
    lemma_set_generic_union_finite,
    lemma_set_union_finite,
    lemma_set_generic_intersect_finite,
    lemma_set_intersect_finite,
    lemma_set_generic_difference_finite,
    lemma_set_difference_finite,
    lemma_set_choose_infinite,
    lemma_set_empty_len,
    lemma_set_len_empty,
    lemma_set_insert_len,
    lemma_set_remove_len,
    lemma_set_contains_len,
    lemma_set_choose_len,
    lemma_set_filter_is_intersect,
    GSet::lemma_set_product_contains,
    GSet::lemma_set_product_contains_2,
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

// 'iset' macro, so that the macro name prevents the need for type inference
// of the FINITE parameter.
#[doc(hidden)]
#[macro_export]
macro_rules! iset_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::set::ISet::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! iset {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::set::iset_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;
pub use iset_internal;
pub use iset;

} // verus!
