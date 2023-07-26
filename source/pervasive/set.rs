use core::marker;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::map::*;

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
/// To prove that two sequences are equal, it is usually easiest to use the [`assert_sets_equal!`](crate::set_lib::assert_sets_equal) macro.

#[verifier(external_body)]
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

    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, s2: Set<A>) -> bool {
        self =~= s2
    }

    /// Returns `true` if the first argument is a subset of the second.

    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
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

    #[verifier(inline)]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.

    pub spec fn intersect(self, s2: Set<A>) -> Set<A>;

    /// Set difference, i.e., the set of all elements in the first one but not in the second.

    pub spec fn difference(self, s2: Set<A>) -> Set<A>;

    /// Set complement (within the space of all possible elements in `A`).

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
        forall |a: A| self.contains(a) ==> !s2.contains(a)
    }
}

// Trusted axioms

/// The empty set contains no elements
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
}

/// A call to `Set::new` with the predicate `f` contains `a` if and only if `f(a)` is true.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_new<A>(f: FnSpec(A) -> bool, a: A)
    ensures
        Set::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of inserting element `a2` into set `s` must contain `a1` if and only if
/// the set contained `a1` before the insertion of `a2` or if `a1` is equal to `a2`
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_contains<A>(s: Set<A>, a1: A, a2: A)
    ensures
        #[trigger] s.insert(a1).contains(a2) <==> a1 == a2 || s.contains(a2),
{}

/// The result of removing element `a` from set `s` must not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,
{
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s` 
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.remove(a2).contains(a1) == s.contains(a1),
{
}

// Changed to match Dafny prelude
/// The union of sets `s1` and `s2` contains element `a` if and only if 
/// `s1` contains `a` and/or `s2` contains `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) <==> (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        s.complement().contains(a) == !s.contains(a),
{
}

/// Sets `s1` and `s2` are equal if and only if they contain all of the same elements.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_mk_map_domain<K, V>(s: Set<K>, f: FnSpec(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_mk_map_index<K, V>(s: Set<K>, f: FnSpec(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        s.mk_map(f)[key] == f(key),
{
}

// Trusted axioms about finite

/// The empty set is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
}

/// The result of removing an element `a` from a finite set `s` is also finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
}

/// The union of two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
}

/// The intersection of two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

/// The set difference between two finite sets is finite.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

/// An infinite set `s` contains the element `s.choose()`.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
}

// Trusted axioms about len

// Note: we could add more axioms about len, but they would be incomplete.
// The following, with axiom_set_ext_equal, are enough to build libraries about len.

/// The empty set has length 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
}

/// The result of inserting an element `a` into a finite set `s` has length 
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) { 0int } else { 1 }),
{
}

/// The result of removing an element `a` from a finite set `s` has length 
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) { 1int } else { 0 }),
{
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
}

// Macros

#[doc(hidden)]
#[macro_export]
macro_rules! set_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::set::Set::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! set {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::set::set_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;

} // verus!
