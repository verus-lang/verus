use core::{marker};

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::set::*;

verus!{

/// `Multiset<V>` is an abstract multiset type for specifications.
///
/// `Multiset<V>` can be encoded as a (total) map from elements to natural numbers,
/// where the number of nonzero entries is finite.
///
/// Multisets can be constructed in a few different ways:
///  * [`Multiset::empty()`] constructs an empty multiset.
///  * By manipulating existings multisets with [`Multiset::add`], [`Multiset::insert`],
///    [`Multiset::sub`], [`Multiset::remove`], or [`Multiset::filter`].
///  * TODO: `multiset!` constructor macro, multiset from set, from map, etc.
///
/// To prove that two multisets are equal, it is usually easiest to use the 
/// [`assert_multisets_equal!`] macro.

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

#[verifier(external_body)]
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

    /// Returns `true` is the left argument is contained in the right argument,
    /// that is, if for each value `v`, the number of occurences in the left
    /// is at most the number of occurences in the right.

    pub open spec fn le(self, m2: Self) -> bool {
        forall |v: V| self.count(v) <= m2.count(v)
    }

    /// Returns `true` if every element in the multiset maps to a valid value
    /// i.e. a value greater than or equal to 0 and less than or equal to the
    /// cardinality of the multiset.

    pub open spec fn is_valid(self) ->bool;

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns true if the two multisets are pointwise equal, i.e.,
    /// for every value `v: V`, the counts are the same in each multiset.
    /// This is equivalent to the multisets actually being equal
    /// by [`axiom_multiset_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_multisets_equal!`] macro, rather than using `ext_equal` directly.

    #[deprecated = "use =~= or =~~= instead"]
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

    pub open spec fn intersection_with(self, other: Self) -> Self;

    /// Returns a multiset containing the difference between the count of a
    /// given element of the two sets.

    pub open spec fn difference_with(self, other: Self) -> Self;

    /// Returns true if the count for any given element in the calling multiset
    /// is less than or equal to the count for the corresponding element
    /// in the argument multiset.

    pub open spec fn subset_of(self, other: Self) -> bool;

    /// Returns true if there exist no elements that have a count greater 
    /// than 0 in both multisets. In other words, returns true if the two
    /// multisets have no elements in common.

    pub open spec fn disjoint_with(self, other: Self) -> bool;

    pub open spec fn min(x: nat, y: nat) -> nat {
        if x <= y {x}
        else {y}
    }

    pub open spec fn clip(x: int) -> nat {
        if x < 0 {0}
        else {x as nat}
    }
}

// Specification of `empty`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_empty<V>(v: V)
    ensures Multiset::empty().count(v) == 0,
{ }

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_empty_len<V>(m: Multiset<V>)
    ensures
        #[trigger] m.len() == 0 <==> m =~= Multiset::empty(),
        #[trigger] m.len() > 0 ==> exists |v: V| 0 < m.count(v),
{}      

// Specification of `singleton`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_singleton<V>(v: V)
    ensures (#[trigger] Multiset::singleton(v)).count(v) == 1,
{ }

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_singleton_different<V>(v: V, w: V)
    ensures v != w ==> Multiset::singleton(v).count(w) == 0,
{ }

// PROBLEMATIC: causes lemma_max_of_concat to fail in seq_lib
// #[verifier(external_body)]
// #[verifier(broadcast_forall)]
// pub proof fn axiom_multiset_singleton_equivalency<V>(v: V)
//     ensures 
//         #[trigger] Multiset::singleton(v) == Multiset::empty().insert(v),
// {}

// Specification of `add`

// Added trigger to match Dafny prelude version
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_add<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures #[trigger] m1.add(m2).count(v) == m1.count(v) + m2.count(v),
{ }

// Specification of `sub`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_sub<V>(m1: Multiset<V>, m2: Multiset<V>, v: V)
    ensures m1.sub(m2).count(v) ==
        if m1.count(v) >= m2.count(v) { m1.count(v) - m2.count(v) } else { 0 },
{ }

// Extensional equality

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_ext_equal<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures #[trigger] (m1 =~= m2) <==> (forall |v: V| m1.count(v) == m2.count(v)),
{ }

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_multiset_ext_equal_deep<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures #[trigger] (m1 =~~= m2) <==> m1 =~= m2,
{ }

// Specification of `len`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_empty<V>()
    ensures (#[trigger] Multiset::<V>::empty().len()) == 0,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_singleton<V>(v: V)
    ensures (#[trigger] Multiset::<V>::singleton(v).len()) == 1,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_add<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures (#[trigger] m1.add(m2).len()) == m1.len() + m2.len(),
{}
// TODO could probably prove this theorem.

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_sub<V>(m1: Multiset<V>, m2: Multiset<V>)
    requires m2.le(m1)
    ensures (#[trigger] m1.sub(m2).len()) == m1.len() - m2.len(),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_count_le_len<V>(m: Multiset<V>, v: V)
    ensures #[trigger] m.count(v) <= #[trigger] m.len()
{}

// Specification of `filter`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_filter_count<V>(m: Multiset<V>, f: FnSpec(V) -> bool, v: V)
    ensures (#[trigger] m.filter(f).count(v)) ==
        if f(v) { m.count(v) } else { 0 }
{}

// Specification of `choose`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_choose_count<V>(m: Multiset<V>)
    requires
        #[trigger] m.len() != 0,
    ensures
        #[trigger] m.count(m.choose()) > 0,
{}

// Specifications of `insert`

// Ported from Dafny prelude
/// If you insert element x into multiset m, then element y maps
/// to a count greater than 0 if and only if x==y or y already
/// mapped to a count greater than 0 before the insertion of x.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_insert_containment<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < #[trigger] m.insert(x).count(y) <==> x == y || 0 < m.count(y)
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_insert_increases_count_by_1<V>(m: Multiset<V>, x: V)
    ensures 
        #[trigger] m.insert(x).count(x) == m.count(x) + 1
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_insert_non_decreasing<V>(m: Multiset<V>, x: V, y: V)
    ensures
        0 < m.count(y) ==> 0 < #[trigger] m.insert(x).count(y),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_insert_other_elements_unchanged<V>(m: Multiset<V>, x: V, y: V)
    ensures
        x != y ==> #[trigger] m.count(y) == #[trigger] m.insert(x).count(y),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_insert_len<V>(m: Multiset<V>, x: V)
    ensures
        #[trigger] m.insert(x).len() == m.len() +1
{}

// Specifications of `intersection_with`

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_intersection_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        #[trigger] a.intersection_with(b).count(x) == Multiset::<V>::min(a.count(x),b.count(x))
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_left_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        #[trigger] a.intersection_with(b).intersection_with(b) == a.intersection_with(b),
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_right_pseudo_idempotence<V>(a: Multiset<V>, b: Multiset<V>)
    ensures
        #[trigger] a.intersection_with(a.intersection_with(b)) == a.intersection_with(b),
{}

// Specification of `difference_with`

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_difference_count<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        #[trigger] a.difference_with(b).count(x) == Multiset::<V>::clip(a.count(x) - b.count(x))
{}

// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_difference_bottoms_out<V>(a: Multiset<V>, b: Multiset<V>, x: V)
    ensures
        #[trigger] a.count(x) <= #[trigger] b.count(x) 
            ==> (#[trigger] a.difference_with(b)).count(x) == 0
{}

// Specification of `subset_of`

// Ported from Dafny prelude
/// Multiset subset means a must have at most as many of each element as b
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_subset_of_specs<V>(a: Multiset<V>, b: Multiset<V>, x:V)
    ensures
        #[trigger] a.subset_of(b) <==> #[trigger] a.count(x) <= #[trigger] b.count(x)
{}

// Specification of `disjoint_with`
// PROBLEMATIC: may cause lemma_no_dup_set_cardinality in seq_lib to run forever
// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_disjointness<V>(a: Multiset<V>, b: Multiset<V>, x:V)
    ensures
        #[trigger] a.disjoint_with(b) <==> 
            (#[trigger] a.count(x) == 0 || #[trigger] b.count(x) == 0)
{}

// Specification of `is_valid`
// PROBLEMATIC: may cause lemma_min_of_concat to fail
// Ported from Dafny prelude
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_is_valid<V>(m: Multiset<V>, bx: V)
    ensures
        m.is_valid() <==> 0 <= #[trigger] m.count(bx) <= m.len(),
{}

#[macro_export]
macro_rules! assert_multisets_equal {
    (::builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_multisets_equal_internal!($m1, $m2)
    };
    (::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_multisets_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_multisets_equal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $m1;
        #[verifier::spec] let m2 = $m2;
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                ::builtin::ensures([
                    ::builtin::equal(m1.count($k), m2.count($k))
                ]);
                { $bblock }
            });
            ::builtin::assert_(m1.ext_equal(m2));
        });
    }
}

pub use assert_multisets_equal;

} // verus!
