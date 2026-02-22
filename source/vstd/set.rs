#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::gmap::GMap;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use core::marker::PhantomData;
use super::gset::*;
#[allow(unused_imports)]
use super::iset::{
    lemma_set_insert_finite,
    lemma_set_remove_finite,
    lemma_iset_map_contains,
    lemma_set_union_finite,
    lemma_set_intersect_finite,
    lemma_set_difference_finite,
    lemma_to_finite_len,
};

verus! {

/// `Set<A>` is a set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
/// Sets are always finite; the constructors only allow construction of finite sets. If you require
/// infinite sets, see `Iset`.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A>(pub GSet<A, Finite>);



impl<A> Set<A> {
    /// Returns the set that contains an element `f(x)` for every element `x` in `self`.
    #[verifier::opaque]
    pub open spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B> {
        Set(self.0.map(f))
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    /// Preserves finiteness of self.
    #[verifier::opaque]
    pub open spec fn filter(self, f: spec_fn(A) -> bool) -> (out: Set<A>) {
        Set(self.0.filter(f))
    }

    /// Replace each element of a set with the elements of another set.
    /// Preserves finiteness of self.
    #[verifier::opaque]
    pub open spec fn product<B>(self, f: spec_fn(A) -> Set<B>) -> (out: Set<B>) {
        Set(self.0.product(|a| f(a).0))
    }

    pub open spec fn to_finite(self) -> Set<A>
        recommends
            self.finite(),
    {
        Set(self.0.cast_finiteness::<Finite>())
    }
}

pub broadcast proof fn lemma_set_finite_from_type<A>(s: Set<A>)
    ensures
        #[trigger] s.finite(),
{
    axiom_gset_finite_from_trait(s.0);
}

pub broadcast proof fn lemma_set_map_contains<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
    reveal(Set::map);
    lemma_gset_map_contains(s.0, f);
    assert forall|y| s.map(f).contains(y) implies (exists|x: A| s.contains(x) && f(x) == y) by {
        // Force the GSet-level bridge with an explicit intermediate
        let gset_mapped: GSet<B, Finite> = s.0.map(f);
        assert(gset_mapped.contains(y));
        // GSet lemma gives: exists|x| s.0.contains(x) && f(x) == y
        let witness = choose|x: A| s.0.contains(x) && f(x) == y;
        assert(s.contains(witness) && f(witness) == y);
    }
}




impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::empty"]
    pub open spec fn empty() -> GSet<A, FINITE> {
        Self { set: |a| false, _phantom: PhantomData }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::full"]
    pub open spec fn full() -> GSet<A, Infinite> {
        GSet::<A, Infinite>::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::contains"]
    pub open spec fn contains(self, a: A) -> bool {
        (self.set)(a)
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
    // TODO(perf): make opaque for verification performance; export insert_same/insert_different
    pub open spec fn insert(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    true
                } else {
                    (self.set)(a2)
                },
            _phantom: PhantomData,
        }
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::remove"]
    // TODO(perf): make opaque for verification performance; export remove_same/remove_different
    pub open spec fn remove(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    false
                } else {
                    (self.set)(a2)
                },
            _phantom: PhantomData,
        }
    }

    /// Union of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `union`; this generic version is mostly useful for writing generic libraries.
    // TODO(perf): make opaque for verification performance; export generic_union_contains
    pub open spec fn generic_union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> GSet<A, Infinite> {
        GSet { set: |a| (self.set)(a) || (s2.set)(a), _phantom: PhantomData }
    }

    /// Intersection of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `intersect`; this generic version is mostly useful for writing generic libraries.
    // TODO(perf): make opaque for verification performance; export generic_intersect_contains
    pub open spec fn generic_intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> GSet<A, Infinite> {
        GSet { set: |a| (self.set)(a) && (s2.set)(a), _phantom: PhantomData }
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    /// Most applications should use the finite- or infinite- specializations
    /// `difference`; this generic version is mostly useful for writing generic libraries.
    // TODO(perf): make opaque for verification performance; export generic_difference_contains
    pub open spec fn generic_difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> GSet<A, Infinite> {
        GSet { set: |a| (self.set)(a) && !(s2.set)(a), _phantom: PhantomData }
    }

    /// Set complement (within the space of all possible elements in `A`).
    // TODO(perf): make opaque for verification performance; export complement_contains
    pub open spec fn complement(self) -> GSet<A, Infinite> {
        GSet { set: |a| !(self.set)(a), _phantom: PhantomData }
    }

    /// Returns `true` if the set is finite.
    pub open spec fn finite(self) -> bool {
        exists|f: spec_fn(A) -> nat, ub: nat|
            {
                &&& #[trigger] trigger_finite(f, ub)
                &&& surj_on(f, self)
                &&& forall|a| self.contains(a) ==> f(a) < ub
            }
    }

    /// Cardinality of the set. (Only meaningful if a set is finite.)
    pub open spec fn len(self) -> nat {
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
    /// The "empty" set.
    pub open spec fn empty() -> Set<A> { Set(GSet::empty()) }

    /// Predicate indicating if the set contains the given element.
    pub open spec fn contains(self, a: A) -> bool {
        self.0.contains(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    #[verifier::opaque]
    pub open spec fn union(self, s2: Set<A>) -> Set<A> {
        Set(GSet { set: |a| (self.0.set)(a) || (s2.0.set)(a), _phantom: PhantomData })
    }

    /// If *either* set in an intersection is finite, the result is finite.
    /// To exploit that knowledge using this method, put the one you know is finite in the `self`
    /// position.
    #[verifier::opaque]
    pub open spec fn intersect(self, s2: Set<A>) -> Set<A> {
        Set(GSet { set: |a| (self.0.set)(a) && (s2.0.set)(a), _phantom: PhantomData })
    }

    #[verifier::opaque]
    pub open spec fn difference(self, s2: Set<A>) -> Set<A> {
        Set(GSet { set: |a| (self.0.set)(a) && !(s2.0.set)(a), _phantom: PhantomData })
    }

    /// `+` operator, synonymous with `union`
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    /// Returns a new set with the given element inserted.
    #[verifier::opaque]
    pub open spec fn insert(self, a: A) -> Set<A> {
        Set(self.0.insert(a))
    }

    /// Returns a new set with the given element removed.
    #[verifier::opaque]
    pub open spec fn remove(self, a: A) -> Set<A> {
        Set(self.0.remove(a))
    }

    /// Returns `true` if the set is finite.
    pub open spec fn finite(self) -> bool {
        self.0.finite()
    }

    /// Cardinality of the set.
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    /// Chooses an arbitrary element of the set.
    pub open spec fn choose(self) -> A {
        self.0.choose()
    }

    /// Returns `true` if the first argument is a subset of the second.
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        self.0.subset_of(s2.0)
    }

    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns `true` if the sets are disjoint.
    pub open spec fn disjoint(self, s2: Set<A>) -> bool {
        self.0.disjoint(s2.0)
    }

    /// Union of two sets of possibly-mixed finiteness.
    pub open spec fn generic_union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        ISet(self.0.generic_union(s2))
    }

    /// Intersection of two sets of possibly-mixed finiteness.
    pub open spec fn generic_intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        ISet(self.0.generic_intersect(s2))
    }

    /// Set difference of possibly-mixed finiteness.
    pub open spec fn generic_difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        ISet(self.0.generic_difference(s2))
    }

    /// Set complement.
    pub open spec fn complement(self) -> ISet<A> {
        ISet(self.0.complement())
    }

    /// Creates a [`Map`] whose domain is the given set.
    #[deprecated = "Use `Map::from_set` instead"]
    pub open spec fn mk_map<V>(self, f: spec_fn(A) -> V) -> Map<A, V> {
        Map::from_set(self.0, f)
    }

    /// The "full" set. Always returns an ISet since the full set is typically infinite.
    pub open spec fn full() -> ISet<A> {
        ISet(GSet::<A, Finite>::full())
    }

    /// Returns `true` if the set is empty.
    pub open spec fn is_empty(self) -> bool {
        self =~= Set::empty()
    }

    /// Cast to ISet (always valid for Set).
    pub open spec fn to_infinite(self) -> ISet<A> {
        ISet(self.0.to_infinite())
    }

    /// Cast finiteness parameter.
    pub open spec fn cast_finiteness<NEWFINITE: Finiteness>(self) -> GSet<A, NEWFINITE> {
        self.0.cast_finiteness()
    }

    /// Two sets are congruent if they contain the same elements.
    pub open spec fn congruent(self, s2: Set<A>) -> bool {
        self.0.congruent(s2.0)
    }

    /// Fold over the set.
    pub open spec fn fold<B>(self, init: B, f: spec_fn(B, A) -> B) -> B {
        self.0.fold(init, f)
    }
}

/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::<A>::empty().contains(a)),
{
}


/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
    reveal(Set::insert);
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
    reveal(Set::insert);
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
    reveal(Set::remove);
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
pub broadcast proof fn lemma_set_remove_different<A>( s: Set<A>, a1: A, a2: A,)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
    reveal(Set::remove);
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
    reveal(Set::union);
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A>( s1: Set<A>, s2: Set<A>, a: A,)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
    reveal(Set::intersect);
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A>( s1: Set<A>, s2: Set<A>, a: A,)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
    reveal(Set::difference);
}

pub broadcast proof fn lemma_set_ext_equal<A>( s1: Set<A>, s2: Set<A>,)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a))
{
    // Backward: forall|a| contains ==> =~=
    if forall|a: A| s1.contains(a) == s2.contains(a) {
        // Bridge through GSet level
        assert forall|a: A| s1.0.contains(a) == s2.0.contains(a) by {
            assert(s1.contains(a) == s2.contains(a));
        }
        lemma_gset_ext_equal(s1.0, s2.0);
        // Now s1.0 =~= s2.0, so s1 =~= s2
    }
    // Forward: =~= ==> forall|a| contains
    if s1 =~= s2 {
        assert(s1.0 =~= s2.0);
        lemma_gset_ext_equal(s1.0, s2.0);
        // Now forall|a| s1.0.contains(a) == s2.0.contains(a)
        assert forall|a: A| s1.contains(a) == s2.contains(a) by {
            // s1.contains(a) == s1.0.contains(a) by definition (both open)
        }
    }
}

/// Sets `s1` and `s2` are definitionally equal if they contain all of the same elements.
pub broadcast proof fn lemma_set_ext_equal_eq<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) ==> s1 == s2,
{
    if s1 =~= s2 {
        assert(s1.0 =~= s2.0);
        lemma_gset_ext_equal_eq(s1.0, s2.0);
        assert(s1 == s2);
    }
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

//////////////////////////////////////////////////////////////////////////////
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    broadcast use lemma_gset_empty_len;
}

pub broadcast proof fn lemma_set_map_insert<A, B>(
    s: Set<A>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    reveal(Set::insert);
    reveal(Set::map);
    lemma_gset_map_insert(s.0, f, a);
}


pub broadcast proof fn lemma_set_map_len<A, B>(
    s: Set<A>,
    f: spec_fn(A) -> B,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.map(f))]
        s.map(f).len() <= s.len(),
    decreases s.len(),
{
    reveal(Set::map);
    lemma_gset_map_len(s.0, f);
}

pub broadcast proof fn lemma_set_len_empty<A>(s: Set<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> Set::<A>::empty() == s,
{
    lemma_gset_len_empty(s.0);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    reveal(Set::insert);
    lemma_gset_insert_len(s.0, a);
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    reveal(Set::remove);
    lemma_gset_remove_len(s.0, a);
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_set_contains_len<A>(s: Set<A>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    lemma_gset_contains_len(s.0, a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_len(s.0);
}

//////////////////////////////////////////////////////////////////////////////

pub broadcast proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] ISet::new(f).contains(a) == f(a),
{
}

pub broadcast proof fn lemma_set_generic_union<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
    lemma_gset_generic_union(s1, s2, a);
}

pub broadcast proof fn lemma_set_generic_intersect<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
    lemma_gset_generic_intersect(s1, s2, a);
}

pub broadcast proof fn lemma_set_generic_difference<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #[trigger] s1.generic_difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
    lemma_gset_generic_difference(s1, s2, a);
}

pub broadcast proof fn lemma_set_complement<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

pub broadcast proof fn lemma_set_ext_equal_deep<A, FINITE: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE>,
)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
    lemma_gset_ext_equal_deep(s1, s2);
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
    lemma_gset_map_subset(s1, s2, f);
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
    lemma_gset_map_finite(s, f);
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
    lemma_gset_filter_finite(s, f);
}

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
    lemma_gset_generic_union_finite(s1, s2);
}

pub broadcast proof fn lemma_set_generic_intersect_finite<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.generic_intersect(s2).finite(),
{
    lemma_gset_generic_intersect_finite(s1, s2);
}

pub broadcast proof fn lemma_set_generic_difference_finite<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.generic_difference(s2).finite(),
{
    lemma_gset_generic_difference_finite(s1, s2);
}

pub broadcast proof fn lemma_set_choose_infinite<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_infinite(s);
}

//////////////////////////////////////////////////////////////////////////////
// Machinery to support range_set
pub trait FiniteRange: Sized {
    spec fn range_iset(lo: Self, hi: Self) -> ISet<Self>;

    spec fn range_len(lo: Self, hi: Self) -> nat;

    proof fn range_properties(lo: Self, hi: Self)
        ensures
            Self::range_iset(lo, hi).finite(),
            Self::range_iset(lo, hi).len() == Self::range_len(lo, hi),
    ;
}

pub broadcast proof fn range_set_properties<A: FiniteRange>(lo: A, hi: A)
    ensures
        (#[trigger] A::range_iset(lo, hi)).finite(),
        A::range_iset(lo, hi).len() == A::range_len(lo, hi),
{
    A::range_properties(lo, hi);
}

pub trait FiniteFull: Sized {
    proof fn full_properties()
        ensures
            ISet::<Self>::full().finite(),
    ;
}

pub broadcast proof fn full_set_properties<A: FiniteFull>()
    ensures
        #![trigger Set::<A>::full()]
        #![trigger ISet::<A>::full()]
        (ISet::<A>::full()).finite(),
{
    A::full_properties();
}

impl<A: FiniteRange> Set<A> {
    #[verifier::inline]
    /// This is a recommended constructor for building finite sets containing a contiguous range of a
    /// numeric type.
    pub open spec fn range(lo: A, hi: A) -> Set<A> {
        A::range_iset(lo, hi).to_finite()
    }

    #[verifier::inline]
    pub open spec fn range_inclusive(lo: A, hi: A) -> Set<A> {
        A::range_iset(lo, hi).insert(hi).to_finite()
    }
}

impl<A: FiniteRange> ISet<A> {
    #[verifier::inline]
    /// This is a recommended constructor for building finite sets containing a contiguous range of a
    /// numeric type.
    pub open spec fn range(lo: A, hi: A) -> ISet<A> {
        A::range_iset(lo, hi)
    }

    #[verifier::inline]
    pub open spec fn range_inclusive(lo: A, hi: A) -> ISet<A> {
        A::range_iset(lo, hi).insert(hi)
    }
}

// Macro to implement the trait for every numeric type. We need a macro here
// because 'as nat' can't be written as a type generic.
macro_rules! range_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteRange for $t {
                    open spec fn range_iset(lo: Self, hi: Self) -> ISet<Self> {
                        ISet::new(|i: Self| lo <= i < hi)
                    }
                    open spec fn range_len(lo: Self, hi: Self) -> nat {
                        if lo <= hi { (hi - lo) as nat } else { 0 }
                    }
                    proof fn range_properties(lo: Self, hi: Self)
                        decreases hi - lo
                    {
                        broadcast use lemma_set_empty_finite;
                        broadcast use super::iset::lemma_iset_empty_len;
                        broadcast use super::iset::lemma_iset_insert_len;

                        if hi <= lo {
                            assert(Self::range_iset(lo, hi).is_empty());
                        } else {
                            let hi1 = (hi - 1) as $t;
                            Self::range_properties(lo, hi1);
                            assert(Self::range_iset(lo, hi) == Self::range_iset(lo, hi1).insert(hi1));
                            lemma_set_insert_finite(Self::range_iset(lo, hi1), hi1);
                        }
                    }
                }
            } // verus!
        )*
    }
}

macro_rules! full_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteFull for $t {
                    proof fn full_properties() {
                        broadcast use lemma_set_insert_finite;

                        assert(ISet::<$t>::full() == ISet::range_inclusive($t::MIN, $t::MAX));
                        <$t as FiniteRange>::range_properties($t::MIN, $t::MAX);
                    }
                }
            } // verus!
        )*
    }
}

// Make Set,ISet::range available for all of the Verus numeric types
range_impls!([
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

// Make ISet::full available for all of the Verus numeric types
full_impls!([
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

//////////////////////////////////////////////////////////////////////////////
#[deprecated = "Use `Set::range` instead"]
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::<int>::range(lo, hi)
}

// filter definition is closed now, so we expose its meaning through this lemma
pub broadcast proof fn lemma_set_filter_is_intersect<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> bool,
)
    ensures
        (#[trigger] s.filter(f)).congruent(s.generic_intersect(ISet::new(f).0)),
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

impl<A: FiniteFull> Set<A> {
    #[verifier::inline]
    pub open spec fn from_finite_type(f: spec_fn(A) -> bool) -> Set<A> {
        ISet::<A>::full().to_finite().filter(f)
    }
}

impl<A> Set<A> {
    /// Set::map_by is like Set::map, but map only takes a forward function fwd: spec_fn(A) -> B,
    /// while map_by also takes a reverse function rev: spec_fn(B) -> A.
    /// This reverse function can make proofs easier
    /// by avoiding the "exists" that appears in lemmas about Set::map.
    /// Example: for a set s: Set<int>, to map each i in s to (i, 10 * i),
    /// we can write either s.map(|i: int| (i, 10 * i))
    /// or s.map_by(|i: int| (i, 10 * i), |p: (int, int)| p.0);
    /// the version with map_by is usually easier to use in proofs.
    pub open spec fn map_by<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A) -> Set<B> {
        ISet::new(|b: B| self.contains(rev(b)) && b == fwd(rev(b))).to_finite()
    }
}

pub broadcast proof fn lemma_map_by<A, B>(sa: Set<A>, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A)
    ensures
        #![trigger sa.map_by(fwd, rev)]
        forall|b: B| #[trigger]
            sa.map_by(fwd, rev).contains(b) <==> sa.contains(rev(b)) && b == fwd(rev(b)),
{
    reveal(Set::map);
    broadcast use {super::gset::group_gset_lemmas_early, super::gset::group_gset_support_lemmas};

    let ib1 = ISet::new(|b: B| sa.contains(rev(b)) && b == fwd(rev(b)));
    let ib2 = sa.map(fwd).to_infinite();
    assert(ib1 == ib2.filter(|b| ib1.contains(b)));
}

pub broadcast group group_set_lemmas {
    super::gset::group_gset_lemmas_early,
    super::gset::group_gset_support_lemmas,
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
    lemma_set_ext_equal_eq,
    lemma_set_ext_equal_deep,
    lemma_set_empty_finite,
    lemma_set_insert_finite,
    lemma_set_remove_finite,
    lemma_set_map_contains,
    lemma_iset_map_contains,
    lemma_set_map_subset,
    lemma_set_map_finite,
    lemma_set_filter_finite,
    lemma_set_map_len,
    lemma_set_map_insert,
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
    range_set_properties,
    lemma_to_finite_len,
    lemma_map_by,
    full_set_properties,
}

} // verus!
