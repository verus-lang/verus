use core::marker;

#[allow(unused_imports)]
use super::map::*;
#[cfg(verus_keep_ghost)]
use super::math::clip;
#[cfg(verus_keep_ghost)]
use super::math::min;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
#[allow(unused_imports)]
use super::set::*;

verus! {

/// `Multiset<V>` is an abstract multiset type for specifications.
///
/// `Multiset<V>` can be encoded as a (total) map from elements to natural numbers,
/// where the number of nonzero entries is finite.
///
/// Multisets can be constructed in a few different ways:
///  * [`Multiset::empty()`] constructs an empty multiset.
///  * [`Multiset::singleton`] constructs a multiset that contains a single element with multiplicity 1.
///  * [`Multiset::new`] constructs a multiset from a map of elements to multiplicities.
///  * By manipulating existings multisets with [`Multiset::add`], [`Multiset::insert`],
///    [`Multiset::sub`], [`Multiset::remove`], [`Multiset::update`], or [`Multiset::filter`].
///  * TODO: `multiset!` constructor macro, multiset from set, from map, etc.
///
/// To prove that two multisets are equal, it is usually easiest to use the
/// extensionality operator `=~=`.
// We could in principle implement the Multiset via an inductive datatype
// and so we can mark its type argument as accept_recursive_types.
// Note: Multiset is finite (in contrast to Set, Map, which are infinite) because it
// isn't entirely obvious how to represent an infinite multiset in the case where
// a single value (v: V) has an infinite multiplicity. It seems to require either:
//   (1) representing multiplicity by an ordinal or cardinal or something
//   (2) limiting each multiplicity to be finite
// (1) would be complicated and it's not clear what the use would be; (2) has some
// weird properties (e.g., you can't in general define a multiset `map` function
// since it might map an infinite number of elements to the same one).
#[verifier::external_body]
#[verifier::ext_equal]
#[verifier::accept_recursive_types(V)]
pub struct Multiset<V> {
    dummy: marker::PhantomData<V>,
}

impl<V> Multiset<V> {
    /// Returns the _count_, or _multiplicity_ of a single value within the multiset.
    pub spec fn count(self, value: V) -> nat;

    /// The total size of the multiset, i.e., the sum of all multiplicities over all values.
    pub spec fn len(self) -> nat;

    /// An empty multiset.
    pub spec fn empty() -> Self;

    /// Creates a multiset whose elements are given by the domain of the map `m` and whose
    /// multiplicities are given by the corresponding values of `m[element]`. The map `m`
    /// must be finite, or else this multiset is arbitrary.
    pub open spec fn from_map(m: Map<V, nat>) -> Self;

    #[cfg_attr(not(verus_verify_core), deprecated = "use from_map instead")]
    pub open spec fn new(m: Map<V, nat>) -> Self {
        Self::from_map(m)
    }

    pub open spec fn from_set(m: Set<V>) -> Self {
        Self::from_map(Map::new(|k| m.contains(k), |v| 1))
    }

    /// A singleton multiset, i.e., a multiset with a single element of multiplicity 1.
    pub spec fn singleton(v: V) -> Self;

    /// Takes the union of two multisets. For a given element, its multiplicity in
    /// the resulting multiset is the sum of its multiplicities in the operands.
    pub spec fn add(self, m2: Self) -> Self;

    /// Takes the difference of two multisets.
    /// The multiplicities of `m2` are subtracted from those of `self`; if any element
    /// occurs more in `m2` then the resulting multiplicity bottoms out at 0.
    /// (See [`axiom_multiset_sub`] for the precise definition.)
    ///
    /// Note in particular that `self == self.sub(m).add(m)` only holds if
    /// `m` is included in `self`.
    pub spec fn sub(self, m2: Self) -> Self;

    /// Inserts one instance the value `v` into the multiset.
    ///
    /// This always increases the total size of the multiset by 1.
    pub open spec fn insert(self, v: V) -> Self {
        self.add(Self::singleton(v))
    }

    /// Removes one instance of the value `v` from the multiset.
    ///
    /// If `v` was absent from the multiset, then the multiset is unchanged.
    pub open spec fn remove(self, v: V) -> Self {
        self.sub(Self::singleton(v))
    }

    /// Updates the multiplicity of the value `v` in the multiset to `mult`.
    pub open spec fn update(self, v: V, mult: nat) -> Self {
        let map = Map::new(
            |key: V| (self.contains(key) || key == v),
            |key: V|
                if key == v {
                    mult
                } else {
                    self.count(key)
                },
        );
        Self::from_map(map)
    }

    /// Returns `true` is the left argument is contained in the right argument,
    /// that is, if for each value `v`, the number of occurences in the left
    /// is at most the number of occurences in the right.
    pub open spec fn subset_of(self, m2: Self) -> bool {
        forall|v: V| self.count(v) <= m2.count(v)
    }

    #[verifier::inline]
    #[cfg_attr(not(verus_verify_core), deprecated = "use m1.subset_of(m2) or m1 <= m2 instead")]
    pub open spec fn le(self, m2: Self) -> bool {
        self.subset_of(m2)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.subset_of(m2)
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns true if the two multisets are pointwise equal, i.e.,
    /// for every value `v: V`, the counts are the same in each multiset.
    /// This is equivalent to the multisets actually being equal
    /// by [`axiom_multiset_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_multisets_equal!`] macro, rather than using `ext_equal` directly.
    #[cfg_attr(not(verus_verify_core), deprecated = "use =~= or =~~= instead")]
    pub open spec fn ext_equal(self, m2: Self) -> bool {
        self =~= m2
    }

    // TODO define this in terms of a more general constructor?
    pub spec fn filter(self, f: impl Fn(V) -> bool) -> Self;

    /// Chooses an arbitrary value of the multiset.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> V {
        choose|v: V| self.count(v) > 0
    }

    /// Predicate indicating if the multiset contains the given value.
    pub open spec fn contains(self, v: V) -> bool {
        self.count(v) > 0
    }

    /// Returns a multiset containing the lower count of a given element
    /// between the two sets. In other words, returns a multiset with only
    /// the elements that "overlap".
    pub open spec fn intersection_with(self, other: Self) -> Self {
        let m = Map::<V, nat>::new(
            |v: V| self.contains(v),
            |v: V| min(self.count(v) as int, other.count(v) as int) as nat,
        );
        Self::from_map(m)
    }

    /// Returns a multiset containing the difference between the count of a
    /// given element of the two sets.
    pub open spec fn difference_with(self, other: Self) -> Self {
        let m = Map::<V, nat>::new(
            |v: V| self.contains(v),
            |v: V| clip(self.count(v) - other.count(v)),
        );
        Self::from_map(m)
    }

    /// Returns true if there exist no elements that have a count greater
    /// than 0 in both multisets. In other words, returns true if the two
    /// multisets have no elements in common.
    pub open spec fn is_disjoint_from(self, other: Self) -> bool {
        forall|x: V| self.count(x) == 0 || other.count(x) == 0
    }

    /// Returns the set of all elements that have a count greater than 0
    pub open spec fn dom(self) -> Set<V> {
        Set::new(|v: V| self.count(v) > 0)
    }
}

// Specification of `empty`
/// The empty multiset maps every element to multiplicity 0
pub broadcast proof fn axiom_multiset_empty<V>(v: V)
    ensures
        #[trigger] Multiset::empty().count(v) == 0,
{
    admit();
}

// This verified lemma used to be an axiom in the Dafny prelude
/// A multiset is equivalent to the empty multiset if and only if it has length 0.
/// If the multiset has length greater than 0, then there exists some element in the
/// multiset that has a count greater than 0.
pub proof fn lemma_multiset_empty_len<V>(m: Multiset<V>)
    ensures
        (m.len() == 0 <==> m =~= Multiset::empty()) && (m.len() > 0 ==> exists|v: V|
            0 < m.count(v)),
{
    admit();
}

// Specifications of `from_map`
/// A call to Multiset::new with input map `m` will return a multiset that maps
/// value `v` to multiplicity `m[v]` if `v` is in the domain of `m`.
pub broadcast proof fn axiom_multiset_contained<V>(m: Map<V, nat>, v: V)
    requires
        m.dom().finite(),
        m.dom().contains(v),
    ensures
        #[trigger] Multiset::from_map(m).count(v) == m[v],
{
    admit();
}

/// A call to Multiset::new with input map `m` will return a multiset that maps
/// value `v` to multiplicity 0 if `v` is not in the domain of `m`.
pub broadcast proof fn axiom_multiset_new_not_contained<V>(m: Map<V, nat>, v: V)
    requires
        m.dom().finite(),
        !m.dom().contains(v),
    ensures
        #[trigger] Multiset::from_map(m).count(v) == 0,
{
    admit();
}

// Specification of `singleton`
/// A call to Multiset::singleton with input value `v` will return a multiset that maps
/// value `v` to multiplicity 1.
pub broadcast proof fn axiom_multiset_singleton<V>(v: V)
    ensures
        (#[trigger] Multiset::singleton(v)).count(v) == 1,
{
    admit();
}

/// A call to Multiset::singleton with input value `v` will return a multiset that maps
/// any value other than `v` to 0
pub broadcast proof fn axiom_multiset_singleton_different<V>(v: V, w: V)
    ensures
        v != w ==> #[trigger] Multiset::singleton(v).count(w) == 0,
{
    admit();
}

// Specification of `add`
/// The count of value `v` in the multiset `m1.add(m2)` is equal to the sum of the
/// counts of `v` in `m1` and `m2` individually.
pub broadcast proof fn axiom_multiset_add<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures
        #[trigger] m1.add(m2).count(v) == m1.count(v) + m2.count(v),
{
    admit();
}

// Specification of `sub`
/// The count of value `v` in the multiset `m1.sub(m2)` is equal to the difference between the
/// count of `v` in `m1` and `m2` individually. However, the difference is cut off at 0 and
/// cannot be negative.
pub broadcast proof fn axiom_multiset_sub<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures
        #[trigger] m1.sub(m2).count(v) == if m1.count(v) >= m2.count(v) {
            m1.count(v) - m2.count(v)
        } else {
            0
        },
{
    admit();
}

// Extensional equality
/// Two multisets are equivalent if and only if they have the same count for every value.
pub broadcast proof fn axiom_multiset_ext_equal<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        #[trigger] (m1 =~= m2) <==> (forall|v: V| m1.count(v) == m2.count(v)),
{
    admit();
}

pub broadcast proof fn axiom_multiset_ext_equal_deep<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> m1 =~= m2,
{
    admit();
}

// Specification of `len`
/// The length of the empty multiset is 0.
pub broadcast proof fn axiom_len_empty<V>()
    ensures
        (#[trigger] Multiset::<V>::empty().len()) == 0,
{
    admit();
}

/// The length of a singleton multiset is 1.
pub broadcast proof fn axiom_len_singleton<V>(v: V)
    ensures
        (#[trigger] Multiset::<V>::singleton(v).len()) == 1,
{
    admit();
}

/// The length of the addition of two multisets is equal to the sum of the lengths of each individual multiset.
pub broadcast proof fn axiom_len_add<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures
        (#[trigger] m1.add(m2).len()) == m1.len() + m2.len(),
{
    admit();
}

// TODO could probably prove this theorem.
/// The length of the subtraction of two multisets is equal to the difference between the lengths of each individual multiset.
pub broadcast proof fn axiom_len_sub<V>(m1: Multiset<V>, m2: Multiset<V>)
    requires
        m2.subset_of(m1),
    ensures
        (#[trigger] m1.sub(m2).len()) == m1.len() - m2.len(),
{
    admit();
}

/// The count for any given value `v` in a multiset `m` must be less than or equal to the length of `m`.
pub broadcast proof fn axiom_count_le_len<V>(m: Multiset<V>, v: V)
    ensures
        #[trigger] m.count(v) <= #[trigger] m.len(),
{
    admit();
}

// Specification of `filter`
/// For a given value `v` and boolean predicate `f`, if `f(v)` is true, then the count of `v` in
/// `m.filter(f)` is the same as the count of `v` in `m`. Otherwise, the count of `v` in `m.filter(f)` is 0.
pub broadcast proof fn axiom_filter_count<V>(m: Multiset<V>, f: spec_fn(V) -> bool, v: V)
    ensures
        (#[trigger] m.filter(f).count(v)) == if f(v) {
            m.count(v)
        } else {
            0
        },
{
    admit();
}

// Specification of `choose`
/// In a nonempty multiset `m`, the `choose` function will return a value that maps to a multiplicity
/// greater than 0 in `m`.
pub broadcast proof fn axiom_choose_count<V>(m: Multiset<V>)
    requires
        #[trigger] m.len() != 0,
    ensures
        #[trigger] m.count(m.choose()) > 0,
{
    admit();
}

// Axiom about finiteness
/// The domain of a multiset (the set of all values that map to a multiplicity greater than 0) is always finite.
// NB this axiom's soundness depends on the inability to learn anything about the entirety of
// Multiset::from_map.dom().
pub broadcast proof fn axiom_multiset_always_finite<V>(m: Multiset<V>)
    ensures
        #[trigger] m.dom().finite(),
{
    admit();
}

pub broadcast group group_multiset_axioms {
    axiom_multiset_empty,
    axiom_multiset_contained,
    axiom_multiset_new_not_contained,
    axiom_multiset_singleton,
    axiom_multiset_singleton_different,
    axiom_multiset_add,
    axiom_multiset_sub,
    axiom_multiset_ext_equal,
    axiom_multiset_ext_equal_deep,
    axiom_len_empty,
    axiom_len_singleton,
    axiom_len_add,
    axiom_len_sub,
    axiom_count_le_len,
    axiom_filter_count,
    axiom_choose_count,
    axiom_multiset_always_finite,
}

// Lemmas about `update`
/// The multiset resulting from updating a value `v` in a multiset `m` to multiplicity `mult` will
/// have a count of `mult` for `v`.
pub proof fn lemma_update_same<V>(m: Multiset<V>, v: V, mult: nat)
    ensures
        m.update(v, mult).count(v) == mult,
{
    broadcast use group_set_axioms, group_map_axioms, group_multiset_axioms;

    let map = Map::new(
        |key: V| (m.contains(key) || key == v),
        |key: V|
            if key == v {
                mult
            } else {
                m.count(key)
            },
    );
    assert(map.dom() =~= m.dom().insert(v));
}

/// The multiset resulting from updating a value `v1` in a multiset `m` to multiplicity `mult` will
/// not change the multiplicities of any other values in `m`.
pub proof fn lemma_update_different<V>(m: Multiset<V>, v1: V, mult: nat, v2: V)
    requires
        v1 != v2,
    ensures
        m.update(v1, mult).count(v2) == m.count(v2),
{
    broadcast use group_set_axioms, group_map_axioms, group_multiset_axioms;

    let map = Map::new(
        |key: V| (m.contains(key) || key == v1),
        |key: V|
            if key == v1 {
                mult
            } else {
                m.count(key)
            },
    );
    assert(map.dom() =~= m.dom().insert(v1));
}

// Lemmas about `insert`
// This verified lemma used to be an axiom in the Dafny prelude
/// If you insert element x into multiset m, then element y maps
/// to a count greater than 0 if and only if x==y or y already
/// mapped to a count greater than 0 before the insertion of x.
pub proof fn lemma_insert_containment<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < m.insert(x).count(y) <==> x == y || 0 < m.count(y),
{
    broadcast use group_multiset_axioms;

}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into multiset `m` will increase the count of `x` in `m` by 1.
pub proof fn lemma_insert_increases_count_by_1<V>(m: Multiset<V>, x: V)
    ensures
        m.insert(x).count(x) == m.count(x) + 1,
{
    broadcast use group_multiset_axioms;

}

// This verified lemma used to be an axiom in the Dafny prelude
/// If multiset `m` maps element `y` to a multiplicity greater than 0, then inserting any element `x`
/// into `m` will not cause `y` to map to a multiplicity of 0. This is a way of saying that inserting `x`
/// will not cause any counts to decrease, because it accounts both for when x == y and when x != y.
pub proof fn lemma_insert_non_decreasing<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < m.count(y) ==> 0 < m.insert(x).count(y),
{
    broadcast use group_multiset_axioms;

}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into a multiset `m` will not change the count of any other element `y` in `m`.
pub proof fn lemma_insert_other_elements_unchanged<V>(m: Multiset<V>, x: V, y: V)
    ensures
        x != y ==> m.count(y) == m.insert(x).count(y),
{
    broadcast use group_multiset_axioms;

}

// This verified lemma used to be an axiom in the Dafny prelude
/// Inserting an element `x` into a multiset `m` will increase the length of `m` by 1.
pub proof fn lemma_insert_len<V>(m: Multiset<V>, x: V)
    ensures
        m.insert(x).len() == m.len() + 1,
{
    broadcast use group_multiset_axioms;

}

// Lemmas about `intersection_with`
// This verified lemma used to be an axiom in the Dafny prelude
/// The multiplicity of an element `x` in the intersection of multisets `a` and `b` will be the minimum
/// count of `x` in either `a` or `b`.
pub proof fn lemma_intersection_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int),
{
    broadcast use group_set_axioms, group_map_axioms, group_multiset_axioms;

    let m = Map::<V, nat>::new(
        |v: V| a.contains(v),
        |v: V| min(a.count(v) as int, b.count(v) as int) as nat,
    );
    assert(m.dom() =~= a.dom());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of multisets `a` and `b` and then taking the resulting multiset's intersection
/// with `b` again is the same as just taking the intersection of `a` and `b` once.
pub proof fn lemma_left_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        a.intersection_with(b).intersection_with(b) =~= a.intersection_with(b),
{
    broadcast use group_multiset_axioms;

    assert forall|x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|x: V| #[trigger]
        a.intersection_with(b).intersection_with(b).count(x) == min(
            a.count(x) as int,
            b.count(x) as int,
        ) by {
        lemma_intersection_count(a.intersection_with(b), b, x);
        assert(min(min(a.count(x) as int, b.count(x) as int) as int, b.count(x) as int) == min(
            a.count(x) as int,
            b.count(x) as int,
        ));
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of multiset `a` with the result of taking the intersection of `a` and `b`
/// is the same as just taking the intersection of `a` and `b` once.
pub proof fn lemma_right_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        a.intersection_with(a.intersection_with(b)) =~= a.intersection_with(b),
{
    broadcast use group_multiset_axioms;

    assert forall|x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|x: V| #[trigger]
        a.intersection_with(a.intersection_with(b)).count(x) == min(
            a.count(x) as int,
            b.count(x) as int,
        ) by {
        lemma_intersection_count(a, a.intersection_with(b), x);
        assert(min(a.count(x) as int, min(a.count(x) as int, b.count(x) as int) as int) == min(
            a.count(x) as int,
            b.count(x) as int,
        ));
    }
}

// Lemmas about `difference_with`
// This verified lemma used to be an axiom in the Dafny prelude
/// The multiplicity of an element `x` in the difference of multisets `a` and `b` will be
/// equal to the difference of the counts of `x` in `a` and `b`, or 0 if this difference is negative.
pub proof fn lemma_difference_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)),
{
    broadcast use group_set_axioms, group_map_axioms, group_multiset_axioms;

    let m = Map::<V, nat>::new(|v: V| a.contains(v), |v: V| clip(a.count(v) - b.count(v)));
    assert(m.dom() =~= a.dom());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If the multiplicity of element `x` is less in multiset `a` than in multiset `b`, then the multiplicity
/// of `x` in the difference of `a` and `b` will be 0.
pub proof fn lemma_difference_bottoms_out<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        a.count(x) <= b.count(x) ==> a.difference_with(b).count(x) == 0,
{
    broadcast use group_multiset_axioms;

    lemma_difference_count(a, b, x);
}

#[macro_export]
macro_rules! assert_multisets_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::multiset::assert_multisets_equal_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! assert_multisets_equal_internal {
    (::builtin::spec_eq($m1:expr, $m2:expr)) => {
        $crate::vstd::multiset::assert_multisets_equal_internal!($m1, $m2)
    };
    (::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::multiset::assert_multisets_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    (crate::builtin::spec_eq($m1:expr, $m2:expr)) => {
        $crate::vstd::multiset::assert_multisets_equal_internal!($m1, $m2)
    };
    (crate::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::multiset::assert_multisets_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        $crate::vstd::multiset::assert_multisets_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $m1;
        #[verifier::spec] let m2 = $m2;
        $crate::vstd::prelude::assert_by($crate::vstd::prelude::equal(m1, m2), {
            $crate::vstd::prelude::assert_forall_by(|$k $( : $t )?| {
                $crate::vstd::prelude::ensures([
                    $crate::vstd::prelude::equal(m1.count($k), m2.count($k))
                ]);
                { $bblock }
            });
            $crate::vstd::prelude::assert_($crate::vstd::prelude::ext_equal(m1, m2));
        });
    }
}

/// Properties of multisets from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_multiset_properties<V>()
    ensures
        forall|m: Multiset<V>, v: V, mult: nat| #[trigger] m.update(v, mult).count(v) == mult,  //from lemma_update_same
        forall|m: Multiset<V>, v1: V, mult: nat, v2: V|
            v1 != v2 ==> #[trigger] m.update(v1, mult).count(v2) == m.count(v2),  //from lemma_update_different
        forall|m: Multiset<V>|
            (#[trigger] m.len() == 0 <==> m =~= Multiset::empty()) && (#[trigger] m.len() > 0
                ==> exists|v: V| 0 < m.count(v)),  //from lemma_multiset_empty_len
        forall|m: Multiset<V>, x: V, y: V|
            0 < #[trigger] m.insert(x).count(y) <==> x == y || 0 < m.count(y),  //from lemma_insert_containment
        forall|m: Multiset<V>, x: V| #[trigger] m.insert(x).count(x) == m.count(x) + 1,  //from lemma_insert_increases_count_by_1
        forall|m: Multiset<V>, x: V, y: V| 0 < m.count(y) ==> 0 < #[trigger] m.insert(x).count(y),  //from lemma_insert_non_decreasing
        forall|m: Multiset<V>, x: V, y: V|
            x != y ==> #[trigger] m.count(y) == #[trigger] m.insert(x).count(y),  //from lemma_insert_other_elements_unchanged
        forall|m: Multiset<V>, x: V| #[trigger] m.insert(x).len() == m.len() + 1,  //from lemma_insert_len
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int),  //from lemma_intersection_count
        forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
            a.intersection_with(b).intersection_with(b) == a.intersection_with(b),  //from lemma_left_pseudo_idempotence
        forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
            a.intersection_with(a.intersection_with(b)) == a.intersection_with(b),  //from lemma_right_pseudo_idempotence
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)),  //from lemma_difference_count
        forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
            a.count(x) <= #[trigger] b.count(x) ==> (#[trigger] a.difference_with(b)).count(x)
                == 0,  //from lemma_difference_bottoms_out
{
    broadcast use group_multiset_axioms;

    assert forall|m: Multiset<V>, v: V, mult: nat| #[trigger]
        m.update(v, mult).count(v) == mult by {
        lemma_update_same(m, v, mult);
    }
    assert forall|m: Multiset<V>, v1: V, mult: nat, v2: V| v1 != v2 implies #[trigger] m.update(
        v1,
        mult,
    ).count(v2) == m.count(v2) by {
        lemma_update_different(m, v1, mult, v2);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
        a.intersection_with(b).count(x) == min(a.count(x) as int, b.count(x) as int) by {
        lemma_intersection_count(a, b, x);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
        a.intersection_with(b).intersection_with(b) == a.intersection_with(b) by {
        lemma_left_pseudo_idempotence(a, b);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>| #[trigger]
        a.intersection_with(a.intersection_with(b)) == a.intersection_with(b) by {
        lemma_right_pseudo_idempotence(a, b);
    }
    assert forall|a: Multiset<V>, b: Multiset<V>, x: V| #[trigger]
        a.difference_with(b).count(x) == clip(a.count(x) - b.count(x)) by {
        lemma_difference_count(a, b, x);
    }
}

#[doc(hidden)]
pub use assert_multisets_equal_internal;
pub use assert_multisets_equal;

} // verus!
