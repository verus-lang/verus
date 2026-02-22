#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use core::marker::PhantomData;
use super::gset::*;

verus! {
/// `ISet<A>` is a set type for specifications.
///
/// An object `set: ISet<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// In general, an ISet might be infinite.
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
pub struct ISet<A>(pub GSet<A, Infinite>);

impl<A> ISet<A> {
    pub open spec fn new(f: spec_fn(A) -> bool) -> ISet<A> {
        ISet(GSet { set: f, _phantom: PhantomData })
    }

    /// The "empty" ISet.
    pub open spec fn empty() -> ISet<A> { ISet(GSet::empty()) }

    /// The "full" ISet, i.e., ISet containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
    pub open spec fn full() -> ISet<A> {
        ISet::empty().complement()
    }

    /// Predicate indicating if the ISet contains the given element.
    pub open spec fn contains(self, a: A) -> bool {
        self.0.contains(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    pub open spec fn union(self, s2: ISet<A>) -> Self {
        ISet::new(|a| self.contains(a) || s2.contains(a))
    }

    pub open spec fn intersect(self, s2: ISet<A>) -> Self {
        ISet::new(|a| self.contains(a) && s2.contains(a))
    }

    pub open spec fn difference(self, s2: ISet<A>) -> Self {
        ISet::new(|a| self.contains(a) && !s2.contains(a))
    }

    /// `+` operator, synonymous with `union`
    pub open spec fn spec_add(self, s2: ISet<A>) -> ISet<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    pub open spec fn spec_mul(self, s2: ISet<A>) -> ISet<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    pub open spec fn spec_sub(self, s2: ISet<A>) -> ISet<A> {
        self.difference(s2)
    }

    /// Returns a new set with the given element inserted.
    pub open spec fn insert(self, a: A) -> ISet<A> {
        ISet(self.0.insert(a))
    }

    /// Returns a new set with the given element removed.
    pub open spec fn remove(self, a: A) -> ISet<A> {
        ISet(self.0.remove(a))
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
    pub open spec fn subset_of(self, s2: ISet<A>) -> bool {
        self.0.subset_of(s2.0)
    }

    pub open spec fn spec_le(self, s2: ISet<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns `true` if the sets are disjoint.
    pub open spec fn disjoint(self, s2: ISet<A>) -> bool {
        self.0.disjoint(s2.0)
    }

    /// Set complement.
    pub open spec fn complement(self) -> ISet<A> {
        ISet(self.0.complement())
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

    /// Cast to Set (only valid if finite).
    pub open spec fn to_finite(self) -> Set<A>
        recommends
            self.finite(),
    {
        Set(self.0.to_finite())
    }

    /// Cast finiteness parameter.
    pub open spec fn cast_finiteness<NEWFINITE: Finiteness>(self) -> GSet<A, NEWFINITE> {
        self.0.cast_finiteness()
    }

    /// Returns the set that contains an element `f(x)` for every element `x` in `self`.
    pub open spec fn map<B>(self, f: spec_fn(A) -> B) -> ISet<B> {
        ISet(self.0.map(f))
    }

    /// Set of all elements satisfying the predicate `f`.
    pub open spec fn filter(self, f: spec_fn(A) -> bool) -> ISet<A> {
        ISet(self.0.filter(f))
    }

    /// Replace each element with the elements of another set.
    pub open spec fn product<B>(self, f: spec_fn(A) -> ISet<B>) -> ISet<B> {
        ISet(self.0.product(|a| f(a).0))
    }

    /// Creates a map whose domain is this set.
    #[deprecated = "Use `IMap::from_set` instead"]
    pub open spec fn mk_map<V>(self, f: spec_fn(A) -> V) -> IMap<A, V> {
        IMap::from_set(self.0, f)
    }

    /// Returns `true` if the set is empty.
    pub open spec fn is_empty(self) -> bool {
        self =~= ISet::empty()
    }

    /// Cast to ISet (identity for ISet).
    pub open spec fn to_infinite(self) -> ISet<A> {
        ISet(self.0.to_infinite())
    }

    /// Two sets are congruent if they contain the same elements.
    pub open spec fn congruent(self, s2: ISet<A>) -> bool {
        self.0.congruent(s2.0)
    }

    /// Fold over the set.
    pub open spec fn fold<B>(self, init: B, f: spec_fn(B, A) -> B) -> B {
        self.0.fold(init, f)
    }
}

pub broadcast proof fn lemma_iset_map_contains<A, B>(s: ISet<A>, f: spec_fn(A) -> B)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
    lemma_gset_map_contains(s.0, f);
    assert forall|y| s.map(f).contains(y) implies (exists|x: A| s.contains(x) && f(x) == y) by {
        // Force the GSet-level bridge with an explicit intermediate
        let gset_mapped: GSet<B, Infinite> = s.0.map(f);
        assert(gset_mapped.contains(y));
        // GSet lemma gives: exists|x| s.0.contains(x) && f(x) == y
        let witness = choose|x: A| s.0.contains(x) && f(x) == y;
        assert(s.contains(witness) && f(witness) == y);
    }
}

/// The empty set contains no elements
pub broadcast proof fn lemma_iset_empty<A>(a: A)
    ensures
        !(#[trigger] ISet::<A>::empty().contains(a)),
{
}

pub broadcast proof fn lemma_iset_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] ISet::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_iset_insert_same<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_iset_insert_different<A>(s: ISet<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_iset_remove_same<A>(s: ISet<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_iset_remove_insert<A>(s: ISet<A>, a: A)
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
            lemma_iset_remove_different(s, aa, a);
            lemma_iset_insert_different(s.remove(a), aa, a);
        }
    };
    assert forall|aa| #![all_triggers] s.contains(aa) implies s.remove(a).insert(a).contains(
        aa,
    ) by {
        if a == aa {
            lemma_iset_insert_same(s.remove(a), a);
        } else {
            lemma_iset_remove_different(s, aa, a);
            lemma_iset_insert_different(s.remove(a), aa, a);
        }
    };
    lemma_iset_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn lemma_iset_remove_different<A>( s: ISet<A>, a1: A, a2: A,)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_iset_intersect<A>( s1: ISet<A>, s2: ISet<A>, a: A,)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_iset_difference<A>( s1: ISet<A>, s2: ISet<A>, a: A,)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_iset_complement<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

pub broadcast proof fn lemma_iset_ext_equal<A>( s1: ISet<A>, s2: ISet<A>,)
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

pub broadcast proof fn lemma_iset_ext_equal_eq<A>(s1: ISet<A>, s2: ISet<A>)
    ensures
        #[trigger] (s1 =~= s2) ==> s1 == s2,
{
    if s1 =~= s2 {
        lemma_gset_ext_equal_eq(s1.0, s2.0);
        assert(s1 == s2);
    }
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
/// This conclusion is automatic for finite `Set`s, but still useful for SMT-`.finite()` `ISet`s.
pub broadcast proof fn lemma_set_insert_finite<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    broadcast use super::gset::group_gset_cast_lemmas;

    lemma_gset_finite_from_type(s.0.to_finite().insert(a));
    super::gset::lemma_congruence_extensionality(s.0, s.0.to_finite());
    s.0.to_finite().insert(a).congruent_infiniteness(s.0.insert(a));
}

/// The result of removing an element `a` from a finite set `s` is also finite.
/// This conclusion is automatic for finite `Set`s, but still useful for SMT-`.finite()` `ISet`s.
pub broadcast proof fn lemma_set_remove_finite<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    broadcast use super::gset::group_gset_cast_lemmas;

    lemma_gset_finite_from_type(s.0.to_finite().remove(a));
    super::gset::lemma_congruence_extensionality(s.0, s.0.to_finite());
    s.0.to_finite().remove(a).congruent_infiniteness(s.0.remove(a));
}

/// The union of two finite sets is finite.
/// This conclusion is automatic for `.union` on finite `Set`s, but helpful for `ISet`s and
/// `generic_union`s.
pub broadcast proof fn lemma_set_union_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
    assert(s1.union(s2) == s1.generic_union(s2.0));
    lemma_gset_generic_union_finite(s1.0, s2.0);
}

/// The intersection of two finite sets is finite.
/// This conclusion is automatic for `.intersect` on finite `Set`s, but helpful for `ISet`s and
/// `generic_intersect`s.
pub broadcast proof fn lemma_set_intersect_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

/// The set difference between two finite sets is finite.
/// This conclusion is automatic for `.difference` on finite `Set`s, but helpful for `ISet`s and
/// `generic_difference`s.
pub broadcast proof fn lemma_set_difference_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

/// An non-`finite()` ISet `s` contains the element `s.choose()`.
/// Note here 'infinite' means not-SMT-finite. To illustrate,
/// ISet::empty() is type-infinite but not SMT-infinite.
pub broadcast proof fn lemma_iset_choose_infinite<A>(s: ISet<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_infinite(s.0)
}

//------------------------------------------------------------------------------

// 'iset' macro, so that the macro name prevents the need for type inference
// of the FINITE parameter.
#[doc(hidden)]
#[macro_export]
macro_rules! iset_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::iset::ISet::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! iset {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::vstd::iset::iset_internal!($($tail)*))
    };
}

pub use iset_internal;
pub use iset;

//////////////////////////////////////////////////////////////////////////////
/// The empty set has length 0.
pub broadcast proof fn lemma_iset_empty_len<A>()
    ensures
        #[trigger] ISet::<A>::empty().len() == 0,
{
    broadcast use lemma_gset_empty_len;
}

pub broadcast proof fn lemma_iset_map_insert<A, B>(
    s: ISet<A>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    lemma_gset_map_insert(s.0, f, a);
}


pub broadcast proof fn lemma_iset_map_len<A, B>(
    s: ISet<A>,
    f: spec_fn(A) -> B,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.map(f))]
        s.map(f).len() <= s.len(),
    decreases s.len(),
{
    lemma_gset_map_len(s.0, f);
}

pub broadcast proof fn lemma_iset_len_empty<A>(s: ISet<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> ISet::<A>::empty() == s,
{
    lemma_gset_len_empty(s.0);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_iset_insert_len<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    lemma_gset_insert_len(s.0, a);
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_iset_remove_len<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    lemma_gset_remove_len(s.0, a);
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_iset_contains_len<A>(s: ISet<A>, a: A)
    requires
        #[trigger] s.contains(a),
        s.finite(),
    ensures
        #[trigger] s.len() != 0,
{
    broadcast use super::gset::group_gset_cast_lemmas;

    assert(s.0.to_finite().contains(a));
    lemma_gset_contains_len(s.0.to_finite(), a);
    // Bridge: s.0.to_finite().len() == s.0.len() via congruent_len
    lemma_gset_finite_from_type(s.0.to_finite());
    s.0.to_finite().congruent_len(s.0);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_iset_choose_len<A>(s: ISet<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_len(s.0);
}

//////////////////////////////////////////////////////////////////////////////

pub broadcast proof fn lemma_to_finite_len<A>(s: ISet<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.to_finite().len() == s.len(),
    decreases s.len(),
{
    broadcast use lemma_gset_empty_len;
    broadcast use lemma_gset_remove_len;
    broadcast use lemma_gset_len_empty;
    broadcast use super::gset::group_gset_cast_lemmas;
    broadcast use lemma_set_remove_finite;
    broadcast use lemma_gset_choose_len;

    if s.len() == 0 {
        super::gset::lemma_congruence_extensionality(s.0.to_finite(), GSet::<A, Finite>::empty());
    } else {
        let x = s.choose();
        lemma_to_finite_len(s.remove(x));
        // Not sure why this required so much more proof than Chris' draft. His draft got to enjoy
        // group_set_lemmas, but I can't figure out which one was doing the work that avoided this
        // step.
        let fr = s.0.to_finite().remove(x);
        let rf = s.remove(x).0.to_finite();
        assert(fr.congruent(rf)) by {
            assert forall|e| fr.contains(e) implies rf.contains(e) by {
                assert(s.contains(e));
            }
            assert forall|e| rf.contains(e) implies fr.contains(e) by {
                assert(s.contains(e));
            }
        }
        super::gset::lemma_congruence_extensionality(s.0.to_finite().remove(x), s.remove(x).0.to_finite());
    }
}

} // verus!
