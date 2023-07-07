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

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_new<A>(f: FnSpec(A) -> bool, a: A)
    ensures
        Set::new(f).contains(a) == f(a),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.insert(a2).contains(a1) == s.contains(a1),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_contains<A>(s: Set<A>, a1: A, a2: A)
    ensures
        #[trigger] s.insert(a1).contains(a2) <==> a1 == a2 || s.contains(a2),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        s.remove(a2).contains(a1) == s.contains(a1),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) <==> (s1.contains(a) || s2.contains(a)),
{
}

// TODO: Could probably be easily proven as a lemma rather than an axiom...
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.union(b).union(b) == a.union(b),
{}

// TODO: Could probably be easily proven as a lemma rather than an axiom...
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_union_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.union(b).union(a) == a.union(b),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

// TODO: Could probably be easily proven as a lemma rather than an axiom...
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] (a.intersect(b)).intersect(b) == a.intersect(b),
{}

// TODO: Could probably be easily proven as a lemma rather than an axiom...
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] (a.intersect(b)).intersect(a) == a.intersect(b),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference2<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        s2.contains(a) ==> !s1.difference(s2).contains(a),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_disjoint<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> (#[trigger](a+b)).difference(a) == b && (a+b).difference(b) == a
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        s.complement().contains(a) == !s.contains(a),
{
}

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

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
}

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

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

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

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
}

// Dafny encodes the second clause with a single directional, although
// it should be fine with both directions?
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_empty_equivalency_len<A>(s: Set<A>)
    ensures
        #[trigger] s.len() == 0 <==> s =~= Set::empty() 
        && s.len() != 0 ==> exists |x: A| s.contains(x),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) { 0int } else { 1 }),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_same_len<A>(s: Set<A>, a: A)
    ensures
        s.contains(a) ==> #[trigger] s.insert(a).len() == s.len(),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_insert_diff_len<A>(s: Set<A>, a: A)
    ensures
        !s.contains(a) ==> #[trigger] s.insert(a).len() == s.len() + 1,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) { 1int } else { 0 }),
{
}

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

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_disjoint_lens<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> #[trigger] (a+b).len() == a.len() + b.len(),
{}

// TODO: This axiom seems extraneous and unnecessary (actually nvm dafny uses it for lemma cardinality of sets)
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_intersect_union_lens<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] (a+b).len() + #[trigger] a.intersect(b).len() == a.len() + b.len(),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_set_difference_len<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.difference(b).len() + b.difference(a).len() + a.intersect(b).len() == (a+b).len() 
            && a.difference(b).len() == a.len() - a.intersect(b).len()
{}

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
