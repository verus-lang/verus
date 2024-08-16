use core::marker;

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
#[verifier::external_body]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(A)]
pub struct Set<A> {
    dummy: marker::PhantomData<A>,
}

impl<A> Set<A> {
    /// The "empty" set.
    pub spec fn empty() -> Set<A>;

    /// Set whose membership is determined by the given boolean predicate.
    pub spec fn new<F: Fn(A) -> bool>(f: F) -> Set<A>;

    /// The "full" set, i.e., set containing every element of type `A`.
    pub open spec fn full() -> Set<A> {
        Set::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
    pub spec fn contains(self, a: A) -> bool;

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns `true` if for every value `a: A`, it is either in both input sets or neither.
    /// This is equivalent to the sets being actually equal
    /// by [`axiom_set_ext_equal`].
    ///
    /// To prove that two sets are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_sets_equal!`](crate::set_lib::assert_sets_equal) macro,
    /// rather than using `.ext_equal` directly.
    #[cfg_attr(not(verus_verify_core), deprecated = "use =~= or =~~= instead")]
    pub open spec fn ext_equal(self, s2: Set<A>) -> bool {
        self =~= s2
    }

    /// Returns `true` if the first argument is a subset of the second.
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    pub spec fn insert(self, a: A) -> Set<A>;

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    pub spec fn remove(self, a: A) -> Set<A>;

    /// Union of two sets.
    pub spec fn union(self, s2: Set<A>) -> Set<A>;

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.
    pub spec fn intersect(self, s2: Set<A>) -> Set<A>;

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub spec fn difference(self, s2: Set<A>) -> Set<A>;

    /// Set complement (within the space of all possible elements in `A`).
    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    pub spec fn complement(self) -> Set<A>;

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub open spec fn filter<F: Fn(A) -> bool>(self, f: F) -> Set<A> {
        self.intersect(Self::new(f))
    }

    /// Returns `true` if the set is finite.
    pub spec fn finite(self) -> bool;

    /// Cardinality of the set. (Only meaningful if a set is finite.)
    pub spec fn len(self) -> nat;

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
    pub spec fn mk_map<V, F: Fn(A) -> V>(self, f: F) -> Map<A, V>;

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint(self, s2: Self) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

// Trusted axioms
/// The empty set contains no elements
pub broadcast proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
    admit();
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
pub broadcast proof fn axiom_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] Set::new(f).contains(a) == f(a),
{
    admit();
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
    admit();
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
    admit();
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
    admit();
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,
{
    admit();
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
    admit();
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
    admit();
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
    admit();
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
    admit();
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
    admit();
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
pub broadcast proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
    admit();
}

pub broadcast proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
    admit();
}

pub broadcast proof fn axiom_mk_map_domain<K, V>(s: Set<K>, f: spec_fn(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,
{
    admit();
}

pub broadcast proof fn axiom_mk_map_index<K, V>(s: Set<K>, f: spec_fn(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        #[trigger] s.mk_map(f)[key] == f(key),
{
    admit();
}

// Trusted axioms about finite
/// The empty set is finite.
pub broadcast proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
    admit();
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
pub broadcast proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    admit();
}

/// The result of removing an element `a` from a finite set `s` is also finite.
pub broadcast proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    admit();
}

/// The union of two finite sets is finite.
pub broadcast proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
    admit();
}

/// The intersection of two finite sets is finite.
pub broadcast proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
    admit();
}

/// The set difference between two finite sets is finite.
pub broadcast proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
    admit();
}

/// An infinite set `s` contains the element `s.choose()`.
pub broadcast proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    admit();
}

// Trusted axioms about len
// Note: we could add more axioms about len, but they would be incomplete.
// The following, with axiom_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    admit();
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
    admit();
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
    admit();
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn axiom_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    admit();
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    admit();
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
