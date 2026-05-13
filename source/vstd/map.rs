use super::gset::{Finite, Finiteness, GSet, Infinite};
use super::iset::ISet;
use super::set::{
    Set,
    lemma_set_ext_equal,
    lemma_set_ext_equal_eq,
};
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

pub(crate) type GenericMap<K, V, FINITE> = super::gmap::GMap<K, V, FINITE>;

#[doc(hidden)]
pub use super::gmap::{
    map,
    imap,
    map_internal,
    imap_internal,
    assert_maps_equal,
    assert_maps_equal_internal,
};

use verus as verus_; // skip verusfmt due to unhandled return-value-pattern
verus_! {

pub trait MapLike<K, V> {
    type FiniteView: Finiteness;

    spec fn as_gmap(self) -> GenericMap<K, V, Self::FiniteView>;
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct Map<K, V>(pub(crate) super::gmap::GMap<K, V, Finite>);

#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct IMap<K, V>(pub(crate) super::gmap::GMap<K, V, Infinite>);

impl<K, V> MapLike<K, V> for Map<K, V> {
    type FiniteView = Finite;

    #[verifier::inline]
    open spec fn as_gmap(self) -> GenericMap<K, V, Finite> {
        self.to_gmap()
    }
}

impl<K, V> MapLike<K, V> for IMap<K, V> {
    type FiniteView = Infinite;

    #[verifier::inline]
    open spec fn as_gmap(self) -> GenericMap<K, V, Infinite> {
        self.to_gmap()
    }
}

impl<K, V, FINITE: Finiteness> MapLike<K, V> for GenericMap<K, V, FINITE> {
    type FiniteView = FINITE;

    #[verifier::inline]
    open spec fn as_gmap(self) -> GenericMap<K, V, FINITE> {
        self
    }
}

impl<K, V> Map<K, V> {
    #[doc(hidden)]
    pub closed spec fn from_gmap(m: super::gmap::GMap<K, V, Finite>) -> Self {
        Map(m)
    }

    #[doc(hidden)]
    pub closed spec fn to_gmap(self) -> super::gmap::GMap<K, V, Finite> {
        self.0
    }

    pub open spec fn from_set(key_set: Set<K>, fv: spec_fn(K) -> V) -> Self {
        Map::from_gmap(super::gmap::GMap::from_set(key_set.to_gset(), fv))
    }

    pub(crate) open spec fn from_gset(key_set: GSet<K, Finite>, fv: spec_fn(K) -> V) -> Self {
        Map::from_gmap(super::gmap::GMap::from_set(key_set, fv))
    }

    #[verifier::inline]
    pub open spec fn new(key_set: Set<K>, fv: spec_fn(K) -> V) -> Self {
        Map::from_set(key_set, fv)
    }

    pub open spec fn empty() -> Self {
        Map::from_gmap(super::gmap::GMap::empty())
    }

    pub open spec fn idom(self) -> ISet<K> {
        self.to_gmap().idom()
    }

    pub open spec fn dom(self) -> Set<K> {
        Set::from_gset(self.to_gmap().dom())
    }

    pub open spec fn contains_key(self, k: K) -> bool {
        self.to_gmap().contains_key(k)
    }

    pub open spec fn contains_value(self, v: V) -> bool {
        self.to_gmap().contains_value(v)
    }

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.to_gmap().contains_pair(k, v)
    }

    #[verifier::inline]
    pub open spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.to_gmap().index(key)
    }

    #[verifier::inline]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    pub open spec fn insert(self, key: K, value: V) -> Self {
        Map::from_gmap(self.to_gmap().insert(key, value))
    }

    #[verifier::inline]
    pub open spec fn update_at_index(self, key: K, value: V) -> Self {
        self.insert(key, value)
    }

    pub open spec fn remove(self, key: K) -> Self {
        Map::from_gmap(self.to_gmap().remove(key))
    }

    pub open spec fn len(self) -> nat {
        self.to_gmap().len()
    }

    #[verifier::inline]
    pub open spec fn is_empty(self) -> bool {
        self.dom().is_empty()
    }

    pub open spec fn kv_pairs(self) -> Set<(K, V)> {
        Set::from_gset(self.to_gmap().dom().map(|k: K| (k, self[k])))
    }

    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        Map::from_gmap(self.to_gmap().union_prefer_right(m2.to_gmap()))
    }

    pub open spec fn remove_keys(self, keys: Set<K>) -> Self {
        Map::from_gmap(self.to_gmap().remove_keys(keys.to_gset()))
    }

    pub open spec fn restrict(self, keys: Set<K>) -> Self {
        Map::from_gmap(self.to_gmap().restrict(keys.to_gset()))
    }

    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> Map<K, W> {
        Map::from_gmap(self.to_gmap().map_entries(f))
    }

    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> Map<K, W> {
        Map::from_gmap(self.to_gmap().map_values(f))
    }

    pub open spec fn invert(self) -> Map<V, K> {
        Map::from_gmap(self.to_gmap().invert())
    }

    pub open spec fn values(self) -> Set<V> {
        self.dom().map(|k: K| self[k])
    }

    pub open spec fn submap_of(self, m2: Self) -> bool {
        self.to_gmap().submap_of(m2.to_gmap())
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    pub open spec fn is_equal_on_key(self, m2: Self, key: K) -> bool {
        self.to_gmap().is_equal_on_key(m2.to_gmap(), key)
    }

    pub open spec fn agrees(self, m2: Self) -> bool {
        self.to_gmap().agrees(m2.to_gmap())
    }

    pub open spec fn is_injective(self) -> bool {
        self.to_gmap().is_injective()
    }

    pub open spec fn congruent(self, m2: Self) -> bool {
        self.to_gmap().congruent(m2.to_gmap())
    }

    pub(crate) open spec fn congruent_generic<FINITE2: Finiteness>(self, m2: GenericMap<K, V, FINITE2>) -> bool {
        self.to_gmap().congruent(m2)
    }

    pub open spec fn to_infinite(self) -> IMap<K, V> {
        IMap::from_gmap(self.to_gmap().to_infinite())
    }

    pub proof fn to_infinite_ensures(self)
        ensures
            self.to_gmap().to_infinite().dom().congruent(self.to_gmap().dom()),
    {
        self.to_gmap().to_infinite_ensures();
    }

    pub proof fn lemma_union_prefer_right(self, m2: Self)
        ensures
            #![trigger (self.union_prefer_right(m2))]
            self.union_prefer_right(m2).dom().to_infinite()
                == self.dom().to_infinite().union(m2.dom().to_infinite()),
            self.union_prefer_right(m2).dom().to_infinite().congruent(
                self.dom().to_infinite().union(m2.dom().to_infinite()),
            ),
            forall|k|
                #![auto]
                self.union_prefer_right(m2).dom().contains(k) ==> self.union_prefer_right(m2)[k]
                    == if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
    {
        self.to_gmap().lemma_union_prefer_right(m2.to_gmap());
        lemma_map_dom_bridge(self.union_prefer_right(m2));
        lemma_map_dom_bridge(self);
        lemma_map_dom_bridge(m2);
        axiom_map_finite_from_type(self.union_prefer_right(m2));
        axiom_map_finite_from_type(self);
        axiom_map_finite_from_type(m2);
        self.union_prefer_right(m2).dom().to_gset().to_infinite_ensures();
        self.dom().to_gset().to_infinite_ensures();
        m2.dom().to_gset().to_infinite_ensures();
        let lhs = self.union_prefer_right(m2).dom().to_infinite();
        let rhs = self.dom().to_infinite().union(m2.dom().to_infinite());
        assert forall|k| lhs.contains(k) == rhs.contains(k) by {
            super::set::lemma_set_to_infinite_contains(self.union_prefer_right(m2).dom(), k);
            super::set::lemma_set_to_infinite_contains(self.dom(), k);
            super::set::lemma_set_to_infinite_contains(m2.dom(), k);
            self.to_gmap().union_prefer_right(m2.to_gmap()).dom().to_infinite_ensures();
            super::gset::lemma_gset_generic_union(self.to_gmap().dom(), m2.to_gmap().dom(), k);
            super::iset::lemma_iset_union(self.dom().to_infinite(), m2.dom().to_infinite(), k);
            assert(self.union_prefer_right(m2).dom().to_gset().contains(k) == self.to_gmap().union_prefer_right(m2.to_gmap()).dom().contains(k));
            assert(self.to_gmap().dom().contains(k) == self.dom().to_gset().contains(k));
            assert(m2.to_gmap().dom().contains(k) == m2.dom().to_gset().contains(k));
            assert(self.to_gmap().union_prefer_right(m2.to_gmap()).dom().contains(k) == self.to_gmap().union_prefer_right(m2.to_gmap()).dom().to_infinite().contains(k));
            assert(self.to_gmap().union_prefer_right(m2.to_gmap()).dom().to_infinite().contains(k) == self.to_gmap().dom().generic_union(m2.to_gmap().dom()).contains(k));
            assert(self.union_prefer_right(m2).dom().contains(k) == (self.dom().contains(k) || m2.dom().contains(k)));
            assert(lhs.contains(k) == self.union_prefer_right(m2).dom().contains(k));
            assert(rhs.contains(k) == (self.dom().to_infinite().contains(k) || m2.dom().to_infinite().contains(k)));
            assert(rhs.contains(k) == (self.dom().contains(k) || m2.dom().contains(k)));
        }
        super::iset::lemma_iset_ext_equal(lhs, rhs);
        assert(lhs =~= rhs);
        super::iset::lemma_iset_ext_equal_eq(lhs, rhs);
    }

    pub proof fn lemma_remove_keys_len(self, keys: Set<K>)
        requires
            keys <= self.dom(),
            keys.finite(),
            self.dom().finite(),
        ensures
            self.remove_keys(keys).dom().len() == self.dom().len() - keys.len(),
        decreases keys.len(),
    {
        lemma_map_dom_bridge(self);
        self.to_gmap().lemma_remove_keys_len(keys.to_gset());
        lemma_map_dom_bridge(self.remove_keys(keys));
    }

    /// Create an empty tracked map.
    ///
    /// This allows us to create a map, which we know is empty, that is _tracked_.
    pub axiom fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == Map::from_gmap(super::gmap::GMap::<K, V, Finite>::empty()),
    ;

    /// Inserts the given `(key, tracked value)` pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.
    pub axiom fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *final(self) == *old(self).insert(key, value),
    ;

    /// Removes the given key and its associated _tracked_ value from the map.
    ///
    /// The key must exist in the map
    pub axiom fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *final(self) == *old(self).remove(key),
            v == old(self)[key],
    ;

    /// Index into a tracked map, getting a tracked borrow of the value
    pub axiom fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    ;

    /// Index into a tracked map, getting a tracked mutable borrow of the value
    pub axiom fn tracked_borrow_mut(tracked &mut self, key: K) -> (tracked v: &mut V)
        requires
            self.dom().contains(key),
        ensures
            *v === old(self).index(key),
            *final(self) === old(self).insert(key, *final(v))
    ;

    /// Split a mutable borrow of a map into two.
    pub axiom fn tracked_borrow_mut_split(tracked &mut self, keys: Set<K>)
        -> (tracked (m1, m2): (&mut Self, &mut Self))
        requires
            keys <= self.dom(),
        ensures
            *m1 == old(self).restrict(keys),
            *m2 == old(self).remove_keys(keys),
            *final(self) == final(m1).union_prefer_right(*final(m2)),
    ;

    /// Change the keys of a map, by reverse lookup in a different map.
    ///
    /// For each `(old_key, new_key)` pair in `key_map`, the new map will have `(new_key, old_map[old_key])`.
    /// Note the new map may be smaller than the old map if the `key_map` omits mappings for some of the old keys.
    pub axiom fn tracked_map_keys<J>(
        tracked old_map: Map<K, V>,
        key_map: Map<J, K>,
    ) -> (tracked new_map: Map<J, V>)
        requires
            forall|j| #![auto] key_map.contains_key(j) ==> old_map.contains_key(key_map[j]),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.contains_key(j1) && key_map.contains_key(j2) ==> key_map[j1]
                    != key_map[j2],
        ensures
            new_map.dom() == key_map.dom(),
            forall|j|
                key_map.dom().contains(j) ==> new_map.dom().contains(j) && #[trigger] new_map.index(
                    j,
                ) == old_map.index(key_map.index(j)),
    {
        let ghost old_map_view = old_map;
        let ghost key_map_view = key_map;
        assert forall|j|
            #![auto]
            key_map.0.dom().contains(j) ==> old_map.0.dom().contains(key_map.0.index(j))
        by {
            lemma_map_dom_contains_field_bridge(key_map_view, j);
            lemma_map_index_field_bridge(key_map_view, j);
            lemma_map_dom_contains_field_bridge(old_map_view, key_map_view.index(j));
        }
        assert forall|j1, j2|
            #![auto]
            !equal(j1, j2) && key_map.0.dom().contains(j1) && key_map.0.dom().contains(j2)
                ==> !equal(key_map.0.index(j1), key_map.0.index(j2))
        by {
            lemma_map_dom_contains_field_bridge(key_map_view, j1);
            lemma_map_dom_contains_field_bridge(key_map_view, j2);
            lemma_map_index_field_bridge(key_map_view, j1);
            lemma_map_index_field_bridge(key_map_view, j2);
        }
        let tracked new_gmap = super::gmap::GMap::<K, V, Finite>::tracked_map_keys(old_map.0, key_map.0);
        let tracked new_map = Map(new_gmap);

        assert forall |j| #[trigger] new_map.dom().contains(j) <==> key_map_view.dom().contains(j) by {
            lemma_map_dom_contains_field_bridge(new_map, j);
            lemma_map_dom_contains_field_bridge(key_map_view, j);
        }

        assert forall |j|
            key_map_view.dom().contains(j) implies new_map.dom().contains(j) && #[trigger] new_map.index(j)
                == old_map_view.index(key_map_view.index(j))
        by {
            lemma_map_dom_contains_field_bridge(new_map, j);
            lemma_map_dom_contains_field_bridge(key_map_view, j);
            lemma_map_index_field_bridge(new_map, j);
            lemma_map_index_field_bridge(key_map_view, j);
            lemma_map_index_field_bridge(old_map_view, key_map_view.index(j));
        }

        new_map
    }

    pub axiom fn tracked_remove_keys(tracked &mut self, keys: Set<K>) -> (tracked out_map: Self)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            *self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    ;

    pub axiom fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    ;

    /// Extract a set of keys (and their corresponding values) out of the map.
    ///
    /// This allows us to split a map based on a subset of the domain.
    pub axiom fn tracked_remove_keys(tracked &mut self, keys: Set<K>) -> (tracked out_map: Map<
        K,
        V,
    >)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            *final(self) == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    ;

    /// Merge a map into a tracked map.
    ///
    /// The new (key, value) pairs take precendece.
    pub axiom fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *final(self) == old(self).union_prefer_right(right),
    ;
}

// Trusted axioms
/* REVIEW: this is simpler than the two separate axioms below -- would this be ok?
pub broadcast axiom fn axiom_map_index_decreases<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key]));
*/

pub broadcast axiom fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
;

// REVIEW: this is currently a special case that is hard-wired into the verifier
// It implements a version of https://github.com/FStarLang/FStar/pull/2954 .
pub broadcast axiom fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
;

/// The domain of the empty map is the empty set
pub broadcast proof fn axiom_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
    broadcast use super::set::group_set_axioms;

    assert(Set::new(|k: K| (|k| None::<V>)(k) is Some) == Set::<K>::empty());
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
pub broadcast proof fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    broadcast use super::set::group_set_axioms;

    assert(m.insert(key, value).dom() =~= m.dom().insert(key));
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
pub broadcast proof fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
pub broadcast proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
pub broadcast proof fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    broadcast use super::set::group_set_axioms;

    assert(m.remove(key).dom() =~= m.dom().remove(key));
}

/// Removing a key-value pair from a map does not change the value mapped to by
/// any other keys in the map.
pub broadcast proof fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
pub broadcast proof fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    broadcast use super::set::group_set_axioms;

    if m1 =~= m2 {
        assert(m1.dom() =~= m2.dom());
        assert(forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]);
    }
    if ({
        &&& m1.dom() =~= m2.dom()
        &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
    }) {
        if m1.mapping != m2.mapping {
            assert(exists|k| #[trigger] (m1.mapping)(k) != (m2.mapping)(k));
            let k = choose|k| #[trigger] (m1.mapping)(k) != (m2.mapping)(k);
            if m1.dom().contains(k) {
                assert(m1[k] == m2[k]);
            }
            assert(false);

pub broadcast proof fn axiom_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    axiom_map_ext_equal(m1, m2);
}

pub broadcast group group_map_axioms {
    axiom_map_index_decreases_finite,
    axiom_map_index_decreases_infinite,
    axiom_map_empty,
    axiom_map_insert_domain,
    axiom_map_insert_same,
    axiom_map_insert_different,
    axiom_map_remove_domain,
    axiom_map_remove_different,
    axiom_map_ext_equal,
    axiom_map_ext_equal_deep,
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! map_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::vstd::map::Map::empty()
            $(.insert($key, $value))*
    }
}

/// Create a map using syntax like `map![key1 => val1, key2 => val, ...]`.
///
/// This is equivalent to `Map::empty().insert(key1, val1).insert(key2, val2)...`.
///
/// Note that this does _not_ require all keys to be distinct. In the case that two
/// or more keys are equal, the resulting map uses the value of the rightmost entry.
#[macro_export]
macro_rules! map {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::map::map_internal!($($tail)*))
    };
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V>(m: Map<K, V>) -> Map<K, V> {
    m
}

#[doc(hidden)]
pub use map_internal;
pub use map;

/// Prove two maps `map1` and `map2` are equal by proving that their values are equal at each key.
///
/// More precisely, `assert_maps_equal!` requires that for each key `k`:
///  * `map1` contains `k` in its domain if and only if `map2` does (`map1.dom().contains(k) <==> map2.dom().contains(k)`)
///  * If they contain `k` in their domains, then their values are equal (`map1.dom().contains(k) && map2.dom().contains(k) ==> map1[k] == map2[k]`)
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_maps_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn insert_remove(m: Map<int, int>, k: int, v: int)
///     requires !m.dom().contains(k)
///     ensures m.insert(k, v).remove(k) == m
/// {
///     let m2 = m.insert(k, v).remove(k);
///     assert_maps_equal!(m == m2);
///     assert(m == m2);
/// }
/// ```
///
/// For more complex cases, a proof may be required for each key:
///
/// ```rust
/// proof fn bitvector_maps() {
///     let m1 = Map::<u64, u64>::new(
///         |key: u64| key & 31 == key,
///         |key: u64| key | 5);
///
///     let m2 = Map::<u64, u64>::new(
///         |key: u64| key < 32,
///         |key: u64| 5 | key);
///
///     assert_maps_equal!(m1 == m2, key => {
///         // Show that the domains of m1 and m2 are the same by showing their predicates
///         // are equivalent.
///         assert_bit_vector((key & 31 == key) <==> (key < 32));
///
///         // Show that the values are the same by showing that these expressions
///         // are equivalent.
///         assert_bit_vector(key | 5 == 5 | key);
///     });
/// }
/// ```
#[macro_export]
macro_rules! assert_maps_equal {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::map::assert_maps_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_maps_equal_internal {
    (::verus_builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_maps_equal_internal!($m1, $m2)
    };
    (::verus_builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_maps_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_maps_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $crate::vstd::map::check_argument_is_map($m1);
        #[verifier::spec] let m2 = $crate::vstd::map::check_argument_is_map($m2);
        $crate::vstd::prelude::assert_by($crate::vstd::prelude::equal(m1, m2), {
            $crate::vstd::prelude::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                $crate::vstd::prelude::ensures([
                    $crate::vstd::prelude::imply(#[verifier::trigger] m1.dom().contains($k), m2.dom().contains($k))
                    && $crate::vstd::prelude::imply(m2.dom().contains($k), m1.dom().contains($k))
                    && $crate::vstd::prelude::imply(m1.dom().contains($k) && m2.dom().contains($k),
                        $crate::vstd::prelude::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            $crate::vstd::prelude::assert_($crate::vstd::prelude::ext_equal(m1, m2));
        });
    }
}

#[doc(hidden)]
pub use assert_maps_equal_internal;
pub use assert_maps_equal;

} // verus!

verus_! { // skip verusfmt, issue with 'final'

impl<K, V> Map<K, V> {
    pub proof fn tracked_map_keys_in_place(tracked &mut self, key_map: Map<K, K>)
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old(self).dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> key_map.index(j1) != key_map.index(j2),
        ensures
            forall|j| #[trigger] final(self).dom().contains(j) == key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> final(self).dom().contains(j) && #[trigger] final(self).index(j)
                    == old(self).index(key_map.index(j)),
    ;

    pub proof fn tracked_to_infinite(tracked self) -> (tracked out: IMap<K, V>)
        ensures
            self.to_gmap().congruent(out.to_gmap()),
    {
        let tracked out = IMap(self.0.tracked_to_infinite());
        out
    }
}

pub broadcast proof fn lemma_map_from_to_gmap<K, V>(m: Map<K, V>)
    ensures
        #[trigger] Map::from_gmap(m.to_gmap()) == m,
{
}

pub proof fn lemma_map_to_from_gmap_public<K, V>(m: super::gmap::GMap<K, V, Finite>)
    ensures
        #[trigger] Map::from_gmap(m).to_gmap() == m,
{
    lemma_map_to_from_gmap(m);
}

pub(crate) broadcast proof fn lemma_map_to_from_gmap<K, V>(m: super::gmap::GMap<K, V, Finite>)
    ensures
        #[trigger] Map::from_gmap(m).to_gmap() == m,
{
}

impl<K, V> IMap<K, V> {
    #[doc(hidden)]
    pub closed spec fn from_gmap(m: super::gmap::GMap<K, V, Infinite>) -> Self {
        IMap(m)
    }

    #[doc(hidden)]
    pub closed spec fn to_gmap(self) -> super::gmap::GMap<K, V, Infinite> {
        self.0
    }

    pub open spec fn from_set(key_set: ISet<K>, fv: spec_fn(K) -> V) -> Self {
        IMap::from_gmap(super::gmap::GMap::from_set(key_set.to_gset(), fv))
    }

    pub(crate) open spec fn from_gset<FINITE2: Finiteness>(key_set: GSet<K, FINITE2>, fv: spec_fn(K) -> V) -> Self {
        IMap::from_gmap(super::gmap::GMap::from_set(key_set.to_infinite(), fv))
    }

    pub open spec fn new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V) -> Self {
        IMap::from_gmap(super::gmap::IMap::new(fk, fv))
    }

    pub open spec fn total(fv: spec_fn(K) -> V) -> Self {
        IMap::new(|k| true, fv)
    }

    pub open spec fn empty() -> Self {
        IMap::from_gmap(super::gmap::GMap::empty())
    }

    pub open spec fn idom(self) -> ISet<K> {
        self.to_gmap().idom()
    }

    pub open spec fn dom(self) -> ISet<K> {
        ISet::from_gset(self.to_gmap().dom())
    }

    pub open spec fn contains_key(self, k: K) -> bool {
        self.to_gmap().contains_key(k)
    }

    pub open spec fn contains_value(self, v: V) -> bool {
        self.to_gmap().contains_value(v)
    }

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.to_gmap().contains_pair(k, v)
    }

    #[verifier::inline]
    pub open spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.to_gmap().index(key)
    }

    #[verifier::inline]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    pub open spec fn insert(self, key: K, value: V) -> Self {
        IMap::from_gmap(self.to_gmap().insert(key, value))
    }

    #[verifier::inline]
    pub open spec fn update_at_index(self, key: K, value: V) -> Self {
        self.insert(key, value)
    }

    pub open spec fn remove(self, key: K) -> Self {
        IMap::from_gmap(self.to_gmap().remove(key))
    }

    pub open spec fn len(self) -> nat {
        self.to_gmap().len()
    }

    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        IMap::from_gmap(self.to_gmap().union_prefer_right(m2.to_gmap()))
    }

    pub proof fn lemma_union_prefer_right(self, m2: Self)
        ensures
            #![trigger (self.union_prefer_right(m2))]
            self.union_prefer_right(m2).dom() == self.dom().union(m2.dom()),
            self.union_prefer_right(m2).dom().congruent(self.dom().union(m2.dom())),
            forall|k|
                #![auto]
                self.union_prefer_right(m2).dom().contains(k) ==> self.union_prefer_right(m2)[k]
                    == if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
    {
        self.to_gmap().lemma_union_prefer_right(m2.to_gmap());
        lemma_imap_dom_bridge(self.union_prefer_right(m2));
        lemma_imap_dom_bridge(self);
        lemma_imap_dom_bridge(m2);
        let lhs = self.union_prefer_right(m2).dom();
        let rhs = self.dom().union(m2.dom());
        assert forall|k| lhs.contains(k) == rhs.contains(k) by {
            super::iset::lemma_iset_union(self.dom(), m2.dom(), k);
            super::gset::lemma_gset_generic_union(self.to_gmap().dom(), m2.to_gmap().dom(), k);
        }
        super::iset::lemma_iset_ext_equal(lhs, rhs);
        assert(lhs =~= rhs);
        super::iset::lemma_iset_ext_equal_eq(lhs, rhs);
    }

    pub open spec fn remove_keys(self, keys: ISet<K>) -> Self {
        IMap::from_gmap(self.to_gmap().remove_keys(keys.to_gset()))
    }

    pub open spec fn restrict(self, keys: ISet<K>) -> Self {
        IMap::from_gmap(self.to_gmap().restrict(keys.to_gset()))
    }

    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> IMap<K, W> {
        IMap::from_gmap(self.to_gmap().map_entries(f))
    }

    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> IMap<K, W> {
        IMap::from_gmap(self.to_gmap().map_values(f))
    }

    pub open spec fn invert(self) -> IMap<V, K> {
        IMap::from_gmap(self.to_gmap().invert())
    }

    pub open spec fn values(self) -> ISet<V> {
        ISet::new(|v: V| self.contains_value(v))
    }

    pub open spec fn submap_of(self, m2: Self) -> bool {
        self.to_gmap().submap_of(m2.to_gmap())
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    pub open spec fn congruent(self, m2: Self) -> bool {
        self.to_gmap().congruent(m2.to_gmap())
    }

    pub(crate) open spec fn congruent_generic<FINITE2: Finiteness>(self, m2: GenericMap<K, V, FINITE2>) -> bool {
        self.to_gmap().congruent(m2)
    }

    pub open spec fn to_finite(self) -> Map<K, V>
        recommends
            self.dom().finite(),
    {
        Map::from_gmap(self.to_gmap().to_finite())
    }

    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == IMap::from_gmap(super::gmap::GMap::<K, V, Infinite>::empty()),
    {
        let tracked out_v = IMap(super::gmap::GMap::<K, V, Infinite>::tracked_empty());
        out_v
    }

    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == old(self).insert(key, value),
    {
        self.0.tracked_insert(key, value);
    }

    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == old(self).remove(key),
            v == old(self)[key],
    {
        let ghost self_view = *self;
        lemma_imap_dom_contains_bridge(self_view, key);
        let tracked v = self.0.tracked_remove(key);
        v
    }

    pub proof fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    {
        lemma_imap_dom_contains_bridge(*self, key);
        self.0.tracked_borrow(key)
    }

    pub proof fn tracked_remove_keys(tracked &mut self, keys: ISet<K>) -> (tracked out_map: Self)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            *self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    {
        let ghost self_view = *self;
        assert(keys.to_gset().subset_of(self_view.to_gmap().dom())) by {
            assert forall |k| #[trigger] keys.to_gset().contains(k) implies self_view.to_gmap().dom().contains(k) by {
                super::iset::lemma_iset_to_from_gset(keys.to_gset());
                assert(keys.contains(k));
                lemma_imap_dom_contains_bridge(self_view, k);
            }
        }
        let tracked out_map = IMap(self.0.tracked_remove_keys(keys.to_gset()));
        out_map
    }

    pub proof fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    {
        self.0.tracked_union_prefer_right(right.0);
    }

    pub proof fn tracked_to_finite(tracked self) -> (tracked out: Map<K, V>)
        requires
            self.dom().finite(),
        ensures
            self.to_gmap().congruent(out.to_gmap()),
    {
        lemma_imap_dom_bridge(self);
        assert(self.to_gmap().dom().finite());
        let tracked out = Map(self.0.tracked_to_finite());
        out
    }
}

pub broadcast proof fn lemma_imap_from_to_gmap<K, V>(m: IMap<K, V>)
    ensures
        #[trigger] IMap::from_gmap(m.to_gmap()) == m,
{
}

pub(crate) broadcast proof fn lemma_imap_to_from_gmap<K, V>(m: super::gmap::GMap<K, V, Infinite>)
    ensures
        #[trigger] IMap::from_gmap(m).to_gmap() == m,
{
}

pub broadcast proof fn axiom_map_finite_from_type<K, V>(m: Map<K, V>)
    ensures
        #[trigger] m.idom().finite(),
        #[trigger] m.dom().finite(),
{
    super::gmap::axiom_map_finite_from_type(m.to_gmap());
    super::set::lemma_set_to_from_gset(m.to_gmap().dom());
    assert(m.dom().to_gset() == m.to_gmap().dom());
    assert(m.dom().finite() == m.dom().to_gset().finite());
    assert(m.dom().finite());
}

pub proof fn lemma_map_dom_bridge<K, V>(m: Map<K, V>)
    ensures
        #[trigger] m.dom().to_gset() == m.to_gmap().dom(),
{
    super::set::lemma_set_to_from_gset(m.to_gmap().dom());
}

pub proof fn lemma_imap_dom_bridge<K, V>(m: IMap<K, V>)
    ensures
        #[trigger] m.dom().to_gset() == m.to_gmap().dom(),
{
    super::iset::lemma_iset_to_from_gset(m.to_gmap().dom());
}

pub proof fn lemma_map_dom_contains_bridge<K, V>(m: Map<K, V>, k: K)
    ensures
        #[trigger] m.to_gmap().dom().contains(k) == m.dom().contains(k),
        #[trigger] m.dom().contains(k) == m.to_gmap().dom().contains(k),
{
    lemma_map_dom_bridge(m);
    assert(m.dom().contains(k) == m.dom().to_gset().contains(k));
    assert(m.dom().to_gset().contains(k) == m.to_gmap().dom().contains(k));
}

pub(crate) proof fn lemma_map_dom_contains_field_bridge<K, V>(m: Map<K, V>, k: K)
    ensures
        #[trigger] m.dom().contains(k) == m.0.dom().contains(k),
        #[trigger] m.0.dom().contains(k) == m.dom().contains(k),
{
    lemma_map_dom_contains_bridge(m, k);
    assert(m.to_gmap().dom().contains(k) == m.0.dom().contains(k));
}

pub(crate) proof fn lemma_map_index_field_bridge<K, V>(m: Map<K, V>, k: K)
    ensures
        m.dom().contains(k) ==> m[k] == m.0[k],
        m.0.dom().contains(k) ==> m[k] == m.0[k],
{
    lemma_map_dom_contains_field_bridge(m, k);
    if m.dom().contains(k) {
        assert(m.to_gmap().dom().contains(k));
        assert(m[k] == m.to_gmap()[k]);
        assert(m.to_gmap()[k] == m.0[k]);
    }
    if m.0.dom().contains(k) {
        assert(m.dom().contains(k));
        assert(m.to_gmap().dom().contains(k));
        assert(m[k] == m.to_gmap()[k]);
        assert(m.to_gmap()[k] == m.0[k]);
    }
}

pub proof fn lemma_imap_dom_contains_bridge<K, V>(m: IMap<K, V>, k: K)
    ensures
        #[trigger] m.to_gmap().dom().contains(k) == m.dom().contains(k),
        #[trigger] m.dom().contains(k) == m.to_gmap().dom().contains(k),
{
    lemma_imap_dom_bridge(m);
    assert(m.dom().contains(k) == m.dom().to_gset().contains(k));
    assert(m.dom().to_gset().contains(k) == m.to_gmap().dom().contains(k));
}

pub broadcast proof fn lemma_imap_contains_key_dom<K, V>(m: IMap<K, V>, k: K)
    ensures
        #[trigger] m.contains_key(k) == m.dom().contains(k),
{
    lemma_imap_dom_contains_bridge(m, k);
}

pub broadcast proof fn lemma_imap_contains_key_implies_dom<K, V>(m: IMap<K, V>, k: K)
    ensures
        #[trigger] m.contains_key(k) ==> m.dom().contains(k),
{
    lemma_imap_contains_key_dom(m, k);
}

pub broadcast proof fn lemma_imap_dom_implies_contains_key<K, V>(m: IMap<K, V>, k: K)
    ensures
        #[trigger] m.dom().contains(k) ==> m.contains_key(k),
{
    lemma_imap_contains_key_dom(m, k);
}

pub broadcast proof fn lemma_map_contains_key_implies_dom<K, V>(m: Map<K, V>, k: K)
    ensures
        #[trigger] m.contains_key(k) ==> m.dom().contains(k),
{
    lemma_map_dom_contains_bridge(m, k);
}

pub broadcast proof fn lemma_map_dom_implies_contains_key<K, V>(m: Map<K, V>, k: K)
    ensures
        #[trigger] m.dom().contains(k) ==> m.contains_key(k),
{
    lemma_map_dom_contains_bridge(m, k);
}

pub broadcast proof fn lemma_map_contains_pair<K, V>(m: Map<K, V>, k: K, v: V)
    ensures
        #[trigger] m.contains_pair(k, v) <==> (m.contains_key(k) && m[k] == v),
{
    lemma_map_contains_key_implies_dom(m, k);
    lemma_map_dom_implies_contains_key(m, k);
    lemma_map_index_field_bridge(m, k);
    if m.contains_pair(k, v) {
        assert(m.to_gmap().contains_pair(k, v));
        assert(m.to_gmap().dom().contains(k));
        assert(m.contains_key(k));
        assert(m.to_gmap()[k] == v);
        assert(m[k] == m.to_gmap()[k]);
    }
    if m.contains_key(k) && m[k] == v {
        assert(m.dom().contains(k));
        assert(m.to_gmap().dom().contains(k));
        assert(m.to_gmap()[k] == m[k]);
        assert(m.to_gmap().contains_pair(k, v));
        assert(m.contains_pair(k, v));
    }
}

pub broadcast proof fn lemma_map_values_contains<K, V>(m: Map<K, V>, v: V)
    ensures
        #[trigger] m.values().contains(v) <==> m.contains_value(v),
{
    super::set::lemma_set_map_contains(m.dom(), |k: K| m[k]);
    assert(m.values().contains(v) <==> (exists|k: K| m.dom().contains(k) && m[k] == v)) by {
        assert(m.values() == m.dom().map(|k: K| m[k]));
    }
    if m.values().contains(v) {
        assert(exists|k: K| m.dom().contains(k) && m[k] == v);
        let witness = choose|k: K| m.dom().contains(k) && m[k] == v;
        lemma_map_dom_contains_bridge(m, witness);
        lemma_map_index_field_bridge(m, witness);
        assert(m.to_gmap().dom().contains(witness));
        assert(m.to_gmap()[witness] == v);
        assert(m.contains_value(v));
    }
    if m.contains_value(v) {
        let witness = choose|k: K| m.to_gmap().dom().contains(k) && m.to_gmap()[k] == v;
        lemma_map_dom_contains_bridge(m, witness);
        lemma_map_index_field_bridge(m, witness);
        assert(m.dom().contains(witness));
        assert(m[witness] == v);
        assert(exists|k: K| m.dom().contains(k) && m[k] == v);
        assert(m.values().contains(v));
    }
}

pub broadcast proof fn lemma_map_insert_values_contains_other<K, V>(
    m: Map<K, V>,
    key: K,
    value: V,
    other: V,
)
    ensures
        #[trigger] m.insert(key, value).values().contains(other) ==> (other == value || m.values().contains(other)),
{
    lemma_map_values_contains(m.insert(key, value), other);
    lemma_map_values_contains(m, other);
    if m.insert(key, value).values().contains(other) {
        assert(m.insert(key, value).contains_value(other));
        if other != value {
            let witness = choose|k: K|
                m.insert(key, value).to_gmap().dom().contains(k)
                    && m.insert(key, value).to_gmap()[k] == other;
            lemma_map_dom_contains_bridge(m.insert(key, value), witness);
            lemma_map_index_field_bridge(m.insert(key, value), witness);
            assert(m.insert(key, value).dom().contains(witness));
            assert(m.insert(key, value)[witness] == other);
            if witness == key {
                lemma_map_insert_same(m, key, value);
                assert(m.insert(key, value)[witness] == value);
                assert(other == m.insert(key, value)[witness]);
                assert(other == value);
                assert(false);
            }
            lemma_map_insert_contains_key(m, key, value, witness);
            assert(m.insert(key, value).contains_key(witness));
            lemma_map_contains_key_implies_dom(m.insert(key, value), witness);
            assert(m.insert(key, value).dom().contains(witness));
            lemma_map_insert_different(m, witness, key, value);
            assert(m.contains_key(witness));
            lemma_map_contains_key_implies_dom(m, witness);
            assert(m.dom().contains(witness));
            assert(m[witness] == other);
            assert(m.contains_value(other));
            assert(m.values().contains(other));
        }
    }
}

pub broadcast proof fn lemma_map_insert_remove_values_contains_other<K, V>(
    m: Map<K, V>,
    insert_key: K,
    remove_key: K,
    insert_value: V,
    other: V,
)
    requires
        insert_key != remove_key,
        other != insert_value,
    ensures
        #[trigger] m.insert(insert_key, insert_value).remove(remove_key).values().contains(other)
            ==> m.remove(remove_key).values().contains(other),
{
    lemma_map_values_contains(m.insert(insert_key, insert_value).remove(remove_key), other);
    lemma_map_values_contains(m.remove(remove_key), other);
    if m.insert(insert_key, insert_value).remove(remove_key).values().contains(other) {
        assert(m.insert(insert_key, insert_value).remove(remove_key).contains_value(other));
        let witness = choose|k: K|
            m.insert(insert_key, insert_value).remove(remove_key).to_gmap().dom().contains(k)
                && m.insert(insert_key, insert_value).remove(remove_key).to_gmap()[k] == other;
        lemma_map_dom_contains_bridge(m.insert(insert_key, insert_value).remove(remove_key), witness);
        lemma_map_index_field_bridge(m.insert(insert_key, insert_value).remove(remove_key), witness);
        assert(m.insert(insert_key, insert_value).remove(remove_key).dom().contains(witness));
        assert(m.insert(insert_key, insert_value).remove(remove_key)[witness] == other);
        lemma_map_contains_key_implies_dom(m.insert(insert_key, insert_value).remove(remove_key), witness);
        assert(m.insert(insert_key, insert_value).remove(remove_key).contains_key(witness));
        if witness == insert_key {
            assert(witness != remove_key);
            lemma_map_remove_different(m.insert(insert_key, insert_value), witness, remove_key);
            assert(
                m.insert(insert_key, insert_value).remove(remove_key)[witness]
                    == m.insert(insert_key, insert_value)[witness]
            );
            lemma_map_insert_same(m, insert_key, insert_value);
            assert(m.insert(insert_key, insert_value)[witness] == insert_value);
            assert(other == m.insert(insert_key, insert_value).remove(remove_key)[witness]);
            assert(other == insert_value);
            assert(false);
        }
        lemma_map_remove_contains_key(m.insert(insert_key, insert_value), remove_key, witness);
        assert(witness != remove_key);
        assert(m.insert(insert_key, insert_value).contains_key(witness));
        lemma_map_remove_different(m.insert(insert_key, insert_value), witness, remove_key);
        lemma_map_insert_contains_key(m, insert_key, insert_value, witness);
        lemma_map_insert_different(m, witness, insert_key, insert_value);
        assert(m.contains_key(witness));
        lemma_map_contains_key_implies_dom(m, witness);
        lemma_map_remove_contains_key(m, remove_key, witness);
        assert(m.remove(remove_key).contains_key(witness));
        lemma_map_remove_different(m, witness, remove_key);
        assert(
            m.insert(insert_key, insert_value).remove(remove_key)[witness]
                == m.insert(insert_key, insert_value)[witness]
        );
        assert(other == m.insert(insert_key, insert_value).remove(remove_key)[witness]);
        assert(m.insert(insert_key, insert_value)[witness] == m[witness]);
        assert(m.remove(remove_key)[witness] == m[witness]);
        assert(m.remove(remove_key)[witness] == other);
        assert(m.remove(remove_key).contains_value(other));
        assert(m.remove(remove_key).values().contains(other));
    }
}

pub broadcast proof fn lemma_imap_contains_pair<K, V>(m: IMap<K, V>, k: K, v: V)
    ensures
        #[trigger] m.contains_pair(k, v) <==> (m.contains_key(k) && m[k] == v),
{
    lemma_imap_contains_key_dom(m, k);
    lemma_imap_index_field_bridge(m, k);
    if m.contains_pair(k, v) {
        assert(m.to_gmap().contains_pair(k, v));
        assert(m.to_gmap().dom().contains(k));
        assert(m.contains_key(k));
        assert(m.to_gmap()[k] == v);
        assert(m[k] == m.to_gmap()[k]);
    }
    if m.contains_key(k) && m[k] == v {
        assert(m.dom().contains(k));
        assert(m.to_gmap().dom().contains(k));
        assert(m.to_gmap()[k] == m[k]);
        assert(m.to_gmap().contains_pair(k, v));
        assert(m.contains_pair(k, v));
    }
}

pub broadcast proof fn lemma_imap_values_contains<K, V>(m: IMap<K, V>, v: V)
    ensures
        #[trigger] m.values().contains(v) <==> m.contains_value(v),
{
    super::iset::lemma_iset_new(|value: V| m.contains_value(value), v);
}

pub broadcast proof fn lemma_imap_contains_value_witness<K, V>(m: IMap<K, V>, v: V)
    ensures
        m.contains_value(v) ==> exists|k: K| #[trigger] m.dom().contains(k) && m[k] == v,
{
    if m.contains_value(v) {
        let witness = choose|k: K| #[trigger] m.to_gmap().dom().contains(k) && m.to_gmap()[k] == v;
        lemma_imap_dom_contains_bridge(m, witness);
        lemma_imap_index_field_bridge(m, witness);
        assert(m.dom().contains(witness));
        assert(m[witness] == v);
    }
}

pub broadcast proof fn lemma_imap_insert_values_contains_other<K, V>(
    m: IMap<K, V>,
    key: K,
    value: V,
    other: V,
)
    ensures
        #[trigger] m.insert(key, value).values().contains(other) ==> (other == value || m.values().contains(other)),
{
    lemma_imap_values_contains(m.insert(key, value), other);
    lemma_imap_values_contains(m, other);
    if m.insert(key, value).values().contains(other) {
        assert(m.insert(key, value).contains_value(other));
        if other != value {
            let witness = choose|k: K|
                m.insert(key, value).to_gmap().dom().contains(k)
                    && m.insert(key, value).to_gmap()[k] == other;
            lemma_imap_dom_contains_bridge(m.insert(key, value), witness);
            lemma_imap_index_field_bridge(m.insert(key, value), witness);
            assert(m.insert(key, value).dom().contains(witness));
            assert(m.insert(key, value)[witness] == other);
            if witness == key {
                lemma_imap_insert_same(m, key, value);
                assert(m.insert(key, value)[witness] == value);
                assert(other == m.insert(key, value)[witness]);
                assert(other == value);
                assert(false);
            }
            lemma_imap_insert_contains_key(m, key, value, witness);
            assert(m.insert(key, value).contains_key(witness));
            lemma_imap_contains_key_dom(m.insert(key, value), witness);
            assert(m.insert(key, value).dom().contains(witness));
            lemma_imap_insert_different(m, witness, key, value);
            assert(m.contains_key(witness));
            lemma_imap_contains_key_dom(m, witness);
            assert(m.dom().contains(witness));
            assert(m[witness] == other);
            assert(m.contains_value(other));
            assert(m.values().contains(other));
        }
    }
}

pub broadcast proof fn lemma_imap_insert_remove_values_contains_other<K, V>(
    m: IMap<K, V>,
    insert_key: K,
    remove_key: K,
    insert_value: V,
    other: V,
)
    requires
        insert_key != remove_key,
        other != insert_value,
    ensures
        #[trigger] m.insert(insert_key, insert_value).remove(remove_key).values().contains(other)
            ==> m.remove(remove_key).values().contains(other),
{
    lemma_imap_values_contains(m.insert(insert_key, insert_value).remove(remove_key), other);
    lemma_imap_values_contains(m.remove(remove_key), other);
    if m.insert(insert_key, insert_value).remove(remove_key).values().contains(other) {
        assert(m.insert(insert_key, insert_value).remove(remove_key).contains_value(other));
        let witness = choose|k: K|
            m.insert(insert_key, insert_value).remove(remove_key).to_gmap().dom().contains(k)
                && m.insert(insert_key, insert_value).remove(remove_key).to_gmap()[k] == other;
        lemma_imap_dom_contains_bridge(m.insert(insert_key, insert_value).remove(remove_key), witness);
        lemma_imap_index_field_bridge(m.insert(insert_key, insert_value).remove(remove_key), witness);
        assert(m.insert(insert_key, insert_value).remove(remove_key).dom().contains(witness));
        assert(m.insert(insert_key, insert_value).remove(remove_key)[witness] == other);
        lemma_imap_contains_key_dom(m.insert(insert_key, insert_value).remove(remove_key), witness);
        assert(m.insert(insert_key, insert_value).remove(remove_key).contains_key(witness));
        if witness == insert_key {
            assert(witness != remove_key);
            lemma_imap_remove_different(m.insert(insert_key, insert_value), witness, remove_key);
            assert(
                m.insert(insert_key, insert_value).remove(remove_key)[witness]
                    == m.insert(insert_key, insert_value)[witness]
            );
            lemma_imap_insert_same(m, insert_key, insert_value);
            assert(m.insert(insert_key, insert_value)[witness] == insert_value);
            assert(other == m.insert(insert_key, insert_value).remove(remove_key)[witness]);
            assert(other == insert_value);
            assert(false);
        }
        lemma_imap_remove_contains_key(m.insert(insert_key, insert_value), remove_key, witness);
        assert(witness != remove_key);
        assert(m.insert(insert_key, insert_value).contains_key(witness));
        lemma_imap_remove_different(m.insert(insert_key, insert_value), witness, remove_key);
        lemma_imap_insert_contains_key(m, insert_key, insert_value, witness);
        lemma_imap_insert_different(m, witness, insert_key, insert_value);
        assert(m.contains_key(witness));
        lemma_imap_contains_key_dom(m, witness);
        lemma_imap_remove_contains_key(m, remove_key, witness);
        assert(m.remove(remove_key).contains_key(witness));
        lemma_imap_remove_different(m, witness, remove_key);
        assert(
            m.insert(insert_key, insert_value).remove(remove_key)[witness]
                == m.insert(insert_key, insert_value)[witness]
        );
        assert(other == m.insert(insert_key, insert_value).remove(remove_key)[witness]);
        assert(m.insert(insert_key, insert_value)[witness] == m[witness]);
        assert(m.remove(remove_key)[witness] == m[witness]);
        assert(m.remove(remove_key)[witness] == other);
        assert(m.remove(remove_key).contains_value(other));
        assert(m.remove(remove_key).values().contains(other));
    }
}

pub(crate) proof fn lemma_imap_dom_contains_field_bridge<K, V>(m: IMap<K, V>, k: K)
    ensures
        #[trigger] m.dom().contains(k) == m.0.dom().contains(k),
        #[trigger] m.0.dom().contains(k) == m.dom().contains(k),
{
    lemma_imap_dom_contains_bridge(m, k);
    assert(m.to_gmap().dom().contains(k) == m.0.dom().contains(k));
}

pub(crate) proof fn lemma_imap_index_field_bridge<K, V>(m: IMap<K, V>, k: K)
    ensures
        m.dom().contains(k) ==> m[k] == m.0[k],
        m.0.dom().contains(k) ==> m[k] == m.0[k],
{
    lemma_imap_dom_contains_field_bridge(m, k);
    if m.dom().contains(k) {
        assert(m.to_gmap().dom().contains(k));
        assert(m[k] == m.to_gmap()[k]);
        assert(m.to_gmap()[k] == m.0[k]);
    }
    if m.0.dom().contains(k) {
        assert(m.dom().contains(k));
        assert(m.to_gmap().dom().contains(k));
        assert(m[k] == m.to_gmap()[k]);
        assert(m.to_gmap()[k] == m.0[k]);
    }
}

pub(crate) proof fn lemma_imap_remove_keys_dom<K, V>(m: IMap<K, V>, keys: ISet<K>)
    ensures
        m.remove_keys(keys).dom() =~= (m.dom() - keys),
{
    m.to_gmap().lemma_remove_keys(keys.to_gset());
    lemma_imap_dom_bridge(m.remove_keys(keys));
    lemma_imap_dom_bridge(m);
    let lhs = m.remove_keys(keys).dom();
    let rhs = m.dom() - keys;
    assert forall|k: K| lhs.contains(k) == rhs.contains(k) by {
        super::iset::lemma_iset_difference(m.dom(), keys, k);
        super::gset::lemma_gset_generic_difference(m.to_gmap().dom(), keys.to_gset(), k);
        assert(m.remove_keys(keys).dom().to_gset().contains(k) == m.remove_keys(keys).to_gmap().dom().contains(k));
        assert(m.remove_keys(keys).to_gmap().dom().contains(k)
            == m.to_gmap().remove_keys(keys.to_gset()).dom().contains(k));
        assert(m.to_gmap().remove_keys(keys.to_gset()).dom().contains(k)
            == m.to_gmap().dom().generic_difference(keys.to_gset()).contains(k));
        assert(m.to_gmap().dom().generic_difference(keys.to_gset()).contains(k)
            == (m.to_gmap().dom().contains(k) && !keys.to_gset().contains(k)));
        assert(m.to_gmap().dom().contains(k) == m.dom().to_gset().contains(k));
        super::iset::lemma_iset_to_from_gset(keys.to_gset());
        assert(keys.to_gset().contains(k) == keys.contains(k));
        assert(m.dom().contains(k) == m.dom().to_gset().contains(k));
    }
    super::iset::lemma_iset_ext_equal(lhs, rhs);
}

pub broadcast proof fn lemma_imap_remove_keys_contains_key<K, V>(m: IMap<K, V>, keys: ISet<K>, k: K)
    ensures
        #[trigger] m.remove_keys(keys).contains_key(k) <==> (m.contains_key(k) && !keys.contains(k)),
        #[trigger] m.remove_keys(keys).dom().contains(k) <==> (m.dom().contains(k) && !keys.contains(k)),
        #[trigger] m.remove_keys(keys).dom().contains(k) ==> m.remove_keys(keys)[k] == m[k],
        m.dom().contains(k) && !keys.contains(k) ==> m.remove_keys(keys)[k] == m[k],
{
    lemma_imap_remove_keys_dom(m, keys);
    m.to_gmap().lemma_remove_keys(keys.to_gset());
    lemma_imap_contains_key_dom(m.remove_keys(keys), k);
    lemma_imap_contains_key_dom(m, k);
    lemma_imap_dom_contains_bridge(m.remove_keys(keys), k);
    lemma_imap_dom_contains_bridge(m, k);
    super::iset::lemma_iset_difference(m.dom(), keys, k);

    assert(m.remove_keys(keys).dom().contains(k) == m.remove_keys(keys).to_gmap().dom().contains(k));
    assert(m.dom().contains(k) == m.to_gmap().dom().contains(k));
    super::iset::lemma_iset_to_from_gset(keys.to_gset());
    assert(keys.to_gset().contains(k) == keys.contains(k));

    assert(m.remove_keys(keys).dom().contains(k) <==> (m.dom().contains(k) && !keys.contains(k)));
    assert(m.remove_keys(keys).contains_key(k) <==> (m.contains_key(k) && !keys.contains(k)));

    if m.remove_keys(keys).dom().contains(k) {
        assert(m.remove_keys(keys).to_gmap().dom().contains(k));
        assert(m.remove_keys(keys).to_gmap()[k] == m.to_gmap()[k]);
        assert(m.remove_keys(keys)[k] == m.remove_keys(keys).to_gmap()[k]);
        assert(m[k] == m.to_gmap()[k]);
    }

    if m.dom().contains(k) && !keys.contains(k) {
        assert(m.remove_keys(keys).dom().contains(k));
        assert(m.remove_keys(keys)[k] == m[k]);
    }
}

pub(crate) proof fn lemma_imap_restrict_dom<K, V>(m: IMap<K, V>, keys: ISet<K>)
    ensures
        m.restrict(keys).dom() =~= m.dom().intersect(keys),
{
    m.to_gmap().lemma_restrict(keys.to_gset());
    lemma_imap_dom_bridge(m.restrict(keys));
    lemma_imap_dom_bridge(m);
    let lhs = m.restrict(keys).dom();
    let rhs = m.dom().intersect(keys);
    assert forall|k: K| lhs.contains(k) == rhs.contains(k) by {
        super::iset::lemma_iset_intersect(m.dom(), keys, k);
        super::gset::lemma_gset_generic_intersect(m.to_gmap().dom(), keys.to_gset(), k);
        assert(m.restrict(keys).dom().to_gset().contains(k) == m.restrict(keys).to_gmap().dom().contains(k));
        assert(m.restrict(keys).to_gmap().dom().contains(k)
            == m.to_gmap().restrict(keys.to_gset()).dom().contains(k));
        assert(m.to_gmap().restrict(keys.to_gset()).dom().contains(k)
            == m.to_gmap().dom().generic_intersect(keys.to_gset()).contains(k));
        assert(m.to_gmap().dom().generic_intersect(keys.to_gset()).contains(k)
            == (m.to_gmap().dom().contains(k) && keys.to_gset().contains(k)));
        assert(m.to_gmap().dom().contains(k) == m.dom().to_gset().contains(k));
        super::iset::lemma_iset_to_from_gset(keys.to_gset());
        assert(keys.to_gset().contains(k) == keys.contains(k));
        assert(m.dom().contains(k) == m.dom().to_gset().contains(k));
    }
    super::iset::lemma_iset_ext_equal(lhs, rhs);
}

pub proof fn lemma_map_insert_bridge<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).to_gmap() == m.to_gmap().insert(key, value),
{
    lemma_map_to_from_gmap(m.to_gmap().insert(key, value));
}

pub proof fn lemma_map_remove_bridge<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).to_gmap() == m.to_gmap().remove(key),
{
    lemma_map_to_from_gmap(m.to_gmap().remove(key));
}

pub broadcast proof fn lemma_finite_new_ensures<K, V>(key_set: Set<K>, fv: spec_fn(K) -> V)
    ensures
        #![trigger(Map::new(key_set, fv))]
        forall|k|
            key_set.contains(k) <==> #[trigger] Map::new(key_set, fv).dom().contains(k),
        forall|k| key_set.contains(k) ==> #[trigger] Map::new(key_set, fv)[k] == fv(k),
        Map::new(key_set, fv).dom() == key_set,
{
    super::gmap::lemma_new_from_set_ensures(key_set.to_gset(), fv);
    lemma_map_dom_bridge(Map::new(key_set, fv));
    assert(Map::new(key_set, fv).to_gmap() == super::gmap::GMap::from_set(key_set.to_gset(), fv));
    assert forall|k|
        key_set.contains(k) <==> #[trigger] Map::new(key_set, fv).dom().contains(k) by {
        super::set::lemma_set_to_from_gset(key_set.to_gset());
        assert(Map::new(key_set, fv).dom().to_gset().contains(k) == Map::new(key_set, fv).to_gmap().dom().contains(k));
        assert(Map::new(key_set, fv).to_gmap().dom().contains(k) == key_set.to_gset().contains(k));
        assert(key_set.to_gset().contains(k) == key_set.contains(k));
    }
    assert forall|k| key_set.contains(k) implies #[trigger] Map::new(key_set, fv)[k] == fv(k) by {
        assert(Map::new(key_set, fv).to_gmap()[k] == fv(k));
    }
    assert forall|k| #[trigger] Map::new(key_set, fv).dom().contains(k) == key_set.contains(k) by {
    }
    super::set::lemma_set_ext_equal(Map::new(key_set, fv).dom(), key_set);
    super::set::lemma_set_ext_equal_eq(Map::new(key_set, fv).dom(), key_set);
}

pub broadcast axiom fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
;

pub broadcast axiom fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
;

pub broadcast proof fn lemma_infinite_new_ensures<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #![trigger(IMap::new(fk, fv))]
        forall|k|
            #![auto]
            fk(k) <==> IMap::new(fk, fv).dom().contains(k),
        forall|k| #![auto] fk(k) ==> IMap::new(fk, fv)[k] == fv(k),
        IMap::new(fk, fv).dom() == ISet::new(fk),
{
    super::gmap::lemma_infinite_new_ensures(fk, fv);
    lemma_imap_to_from_gmap(super::gmap::IMap::new(fk, fv));
    assert(IMap::new(fk, fv).to_gmap() == super::gmap::IMap::new(fk, fv));
    lemma_imap_dom_bridge(IMap::new(fk, fv));
    assert(IMap::new(fk, fv).dom().to_gset() == ISet::new(fk).to_gset());
    assert forall|k| fk(k) <==> IMap::new(fk, fv).dom().contains(k) by {
        super::iset::lemma_iset_new(fk, k);
    }
    assert forall|k| IMap::new(fk, fv).dom().contains(k) == ISet::new(fk).contains(k) by {
    }
    super::iset::lemma_iset_ext_equal(IMap::new(fk, fv).dom(), ISet::new(fk));
    super::iset::lemma_iset_ext_equal_eq(IMap::new(fk, fv).dom(), ISet::new(fk));
}

pub broadcast proof fn lemma_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
    broadcast use super::gmap::lemma_map_empty;
}

pub broadcast proof fn lemma_imap_empty<K, V>(k: K)
    ensures
        !(#[trigger] IMap::<K, V>::empty().contains_key(k)),
{
    broadcast use super::gmap::lemma_map_empty;
    lemma_imap_contains_key_dom(IMap::<K, V>::empty(), k);
    assert(IMap::<K, V>::empty().to_gmap().dom() == GSet::<K, Infinite>::empty());
    assert(!IMap::<K, V>::empty().to_gmap().dom().contains(k));
}

pub broadcast proof fn lemma_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    super::gmap::lemma_map_insert_domain(m.to_gmap(), key, value);
    lemma_map_insert_bridge(m, key, value);
    lemma_map_dom_bridge(m.insert(key, value));
    lemma_map_dom_bridge(m);
    reveal(Set::insert);
    super::set::lemma_set_to_from_gset(m.to_gmap().dom().insert(key));
    assert forall|k: K| #[trigger] m.insert(key, value).dom().contains(k) == m.dom().insert(key).contains(k) by {
        assert(m.insert(key, value).dom().to_gset().contains(k) == m.to_gmap().insert(key, value).dom().contains(k));
        assert(m.to_gmap().insert(key, value).dom().contains(k) == m.to_gmap().dom().insert(key).contains(k));
        assert(m.dom().insert(key).to_gset().contains(k) == m.to_gmap().dom().insert(key).contains(k));
    }
    lemma_set_ext_equal_eq(m.insert(key, value).dom(), m.dom().insert(key));
}

pub broadcast proof fn lemma_map_insert_contains_key<K, V>(m: Map<K, V>, key: K, value: V, other_key: K)
    ensures
        #[trigger] m.insert(key, value).contains_key(other_key) <==> (other_key == key || m.contains_key(other_key)),
{
    lemma_map_insert_domain(m, key, value);
    lemma_map_contains_key_implies_dom(m, other_key);
    lemma_map_dom_implies_contains_key(m, other_key);
    lemma_map_contains_key_implies_dom(m.insert(key, value), other_key);
    lemma_map_dom_implies_contains_key(m.insert(key, value), other_key);
    assert(m.insert(key, value).dom().contains(other_key) == m.dom().insert(key).contains(other_key));
    if other_key == key {
        super::set::lemma_set_insert_same(m.dom(), key);
        assert(m.dom().insert(key).contains(other_key));
    } else {
        super::set::lemma_set_insert_different(m.dom(), other_key, key);
        assert(m.dom().insert(key).contains(other_key) == m.dom().contains(other_key));
    }
    assert(m.insert(key, value).contains_key(other_key) <==> (other_key == key || m.contains_key(other_key)));
}

pub broadcast proof fn lemma_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
    super::gmap::lemma_map_insert_same(m.to_gmap(), key, value);
}

pub broadcast proof fn lemma_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
    super::gmap::lemma_map_insert_different(m.to_gmap(), key1, key2, value);
}

pub broadcast proof fn lemma_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    super::gmap::lemma_map_remove_domain(m.to_gmap(), key);
    lemma_map_remove_bridge(m, key);
    lemma_map_dom_bridge(m.remove(key));
    lemma_map_dom_bridge(m);
    reveal(Set::remove);
    super::set::lemma_set_to_from_gset(m.to_gmap().dom().remove(key));
    assert forall|k: K| #[trigger] m.remove(key).dom().contains(k) == m.dom().remove(key).contains(k) by {
        assert(m.remove(key).dom().to_gset().contains(k) == m.to_gmap().remove(key).dom().contains(k));
        assert(m.to_gmap().remove(key).dom().contains(k) == m.to_gmap().dom().remove(key).contains(k));
        assert(m.dom().remove(key).to_gset().contains(k) == m.to_gmap().dom().remove(key).contains(k));
    }
    lemma_set_ext_equal_eq(m.remove(key).dom(), m.dom().remove(key));
}

pub broadcast proof fn lemma_map_remove_contains_key<K, V>(m: Map<K, V>, key: K, other_key: K)
    ensures
        #[trigger] m.remove(key).contains_key(other_key) <==> (other_key != key && m.contains_key(other_key)),
{
    lemma_map_remove_domain(m, key);
    lemma_map_contains_key_implies_dom(m, other_key);
    lemma_map_dom_implies_contains_key(m, other_key);
    lemma_map_contains_key_implies_dom(m.remove(key), other_key);
    lemma_map_dom_implies_contains_key(m.remove(key), other_key);
    assert(m.remove(key).dom().contains(other_key) == m.dom().remove(key).contains(other_key));
    if other_key == key {
        super::set::lemma_set_remove_same(m.dom(), key);
        assert(!m.dom().remove(key).contains(other_key));
    } else {
        super::set::lemma_set_remove_different(m.dom(), other_key, key);
        assert(m.dom().remove(key).contains(other_key) == m.dom().contains(other_key));
    }
    assert(m.remove(key).contains_key(other_key) <==> (other_key != key && m.contains_key(other_key)));
}

pub broadcast proof fn lemma_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
    super::gmap::lemma_map_remove_different(m.to_gmap(), key1, key2);
}

pub broadcast proof fn lemma_map_remove_keys_contains_key<K, V>(m: Map<K, V>, keys: Set<K>, k: K)
    ensures
        #[trigger] m.remove_keys(keys).contains_key(k) <==> (m.contains_key(k) && !keys.contains(k)),
        #[trigger] m.remove_keys(keys).dom().contains(k) <==> (m.dom().contains(k) && !keys.contains(k)),
        #[trigger] m.remove_keys(keys).dom().contains(k) ==> m.remove_keys(keys)[k] == m[k],
        m.dom().contains(k) && !keys.contains(k) ==> m.remove_keys(keys)[k] == m[k],
{
    m.to_gmap().lemma_remove_keys(keys.to_gset());
    lemma_map_contains_key_implies_dom(m.remove_keys(keys), k);
    lemma_map_dom_implies_contains_key(m.remove_keys(keys), k);
    lemma_map_contains_key_implies_dom(m, k);
    lemma_map_dom_implies_contains_key(m, k);
    lemma_map_dom_contains_bridge(m.remove_keys(keys), k);
    lemma_map_dom_contains_bridge(m, k);

    assert(m.remove_keys(keys).dom().contains(k) == m.remove_keys(keys).to_gmap().dom().contains(k));
    assert(m.dom().contains(k) == m.to_gmap().dom().contains(k));
    assert(keys.contains(k) == keys.to_gset().contains(k));

    assert(m.remove_keys(keys).dom().contains(k) <==> (m.dom().contains(k) && !keys.contains(k)));
    assert(m.remove_keys(keys).contains_key(k) <==> (m.contains_key(k) && !keys.contains(k)));

    if m.remove_keys(keys).dom().contains(k) {
        assert(m.remove_keys(keys).to_gmap().dom().contains(k));
        assert(m.remove_keys(keys).to_gmap()[k] == m.to_gmap()[k]);
        assert(m.remove_keys(keys)[k] == m.remove_keys(keys).to_gmap()[k]);
        assert(m[k] == m.to_gmap()[k]);
    }

    if m.dom().contains(k) && !keys.contains(k) {
        assert(m.remove_keys(keys).dom().contains(k));
        assert(m.remove_keys(keys)[k] == m[k]);
    }
}

pub broadcast proof fn lemma_imap_insert_contains_key<K, V>(m: IMap<K, V>, key: K, value: V, other_key: K)
    ensures
        #[trigger] m.insert(key, value).contains_key(other_key) <==> (other_key == key || m.contains_key(other_key)),
{
    lemma_imap_contains_key_dom(m.insert(key, value), other_key);
    lemma_imap_contains_key_dom(m, other_key);
    super::gmap::lemma_map_insert_domain(m.to_gmap(), key, value);
}

pub broadcast proof fn lemma_imap_insert_same<K, V>(m: IMap<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
    super::gmap::lemma_map_insert_same(m.to_gmap(), key, value);
}

pub broadcast proof fn lemma_imap_insert_different<K, V>(m: IMap<K, V>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
    super::gmap::lemma_map_insert_different(m.to_gmap(), key1, key2, value);
}

pub broadcast proof fn lemma_imap_remove_contains_key<K, V>(m: IMap<K, V>, key: K, other_key: K)
    ensures
        #[trigger] m.remove(key).contains_key(other_key) <==> (other_key != key && m.contains_key(other_key)),
{
    lemma_imap_contains_key_dom(m.remove(key), other_key);
    lemma_imap_contains_key_dom(m, other_key);
    super::gmap::lemma_map_remove_domain(m.to_gmap(), key);
}

pub broadcast proof fn lemma_imap_remove_different<K, V>(m: IMap<K, V>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
    super::gmap::lemma_map_remove_different(m.to_gmap(), key1, key2);
}

pub broadcast proof fn lemma_imap_remove_absent<K, V>(m: IMap<K, V>, key: K)
    requires
        !m.contains_key(key),
    ensures
        #[trigger] m.remove(key) == m,
{
    assert(m.remove(key) =~= m) by {
        assert forall|other_key: K| #[trigger] m.remove(key).dom().contains(other_key) == m.dom().contains(other_key) by {
            lemma_imap_contains_key_dom(m.remove(key), other_key);
            lemma_imap_contains_key_dom(m, other_key);
            lemma_imap_remove_contains_key(m, key, other_key);
            if other_key == key {
                assert(!m.dom().contains(other_key));
            }
        }
        super::iset::lemma_iset_ext_equal(m.remove(key).dom(), m.dom());
        assert forall|other_key: K| #[trigger] m.remove(key).dom().contains(other_key)
            implies m.remove(key)[other_key] == m[other_key] by {
            if m.remove(key).dom().contains(other_key) {
                lemma_imap_contains_key_dom(m.remove(key), other_key);
                lemma_imap_contains_key_dom(m, other_key);
                lemma_imap_remove_contains_key(m, key, other_key);
                assert(m.remove(key).contains_key(other_key));
                assert(m.contains_key(other_key));
                assert(other_key != key);
                lemma_imap_remove_different(m, other_key, key);
            }
        }
        lemma_imap_ext_equal(m.remove(key), m);
    }
    lemma_imap_ext_equal_eq(m.remove(key), m);
}

pub broadcast proof fn lemma_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    super::gmap::lemma_map_ext_equal(m1.to_gmap(), m2.to_gmap());
    lemma_map_dom_bridge(m1);
    lemma_map_dom_bridge(m2);
    if m1 =~= m2 {
        assert(m1.to_gmap() =~= m2.to_gmap());
        assert(m1.to_gmap().dom() =~= m2.to_gmap().dom());
        assert forall|k: K| m1.dom().contains(k) == m2.dom().contains(k) by {
            assert(m1.dom().to_gset().contains(k) == m1.to_gmap().dom().contains(k));
            assert(m2.dom().to_gset().contains(k) == m2.to_gmap().dom().contains(k));
        }
        lemma_set_ext_equal(m1.dom(), m2.dom());
        assert forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k] by {
            if m1.dom().contains(k) {
                lemma_map_dom_contains_bridge(m1, k);
                lemma_map_dom_contains_bridge(m2, k);
                assert(m1.to_gmap().dom().contains(k) == m1.dom().contains(k));
                assert(m1.to_gmap().dom().contains(k));
                assert(m1.to_gmap().dom().contains(k) == m2.to_gmap().dom().contains(k));
                assert(m2.to_gmap().dom().contains(k));
                assert(m1.to_gmap()[k] == m2.to_gmap()[k]);
                assert(m1[k] == m1.to_gmap()[k]);
                assert(m2[k] == m2.to_gmap()[k]);
            }
        }
    }
    if ({
        &&& m1.dom() =~= m2.dom()
        &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
    }) {
        lemma_set_ext_equal(m1.dom(), m2.dom());
        assert forall|k: K| m1.to_gmap().dom().contains(k) == m2.to_gmap().dom().contains(k) by {
            assert(m1.dom().to_gset().contains(k) == m1.to_gmap().dom().contains(k));
            assert(m2.dom().to_gset().contains(k) == m2.to_gmap().dom().contains(k));
            assert(m1.dom().contains(k) == m2.dom().contains(k));
        }
        super::gset::lemma_gset_ext_equal(m1.to_gmap().dom(), m2.to_gmap().dom());
        assert forall|k: K| #![auto] m1.to_gmap().dom().contains(k) ==> m1.to_gmap()[k] == m2.to_gmap()[k] by {
            if m1.to_gmap().dom().contains(k) {
                lemma_map_dom_contains_bridge(m1, k);
                lemma_map_dom_contains_bridge(m2, k);
                assert(m1.to_gmap().dom().contains(k) == m1.dom().contains(k));
                assert(m1.dom().contains(k));
                assert(m1[k] == m2[k]);
                assert(m1[k] == m1.to_gmap()[k]);
                assert(m2[k] == m2.to_gmap()[k]);
            }
        }
        assert(m1.to_gmap() =~= m2.to_gmap());
        assert(m1 =~= m2);
    }
}

pub broadcast proof fn lemma_map_ext_equal_eq<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) ==> m1 == m2,
{
    if m1 =~= m2 {
        super::gmap::lemma_map_ext_equal_eq(m1.to_gmap(), m2.to_gmap());
        assert(m1.to_gmap() == m2.to_gmap());
        assert(m1 == m2);
    }
}

pub broadcast proof fn lemma_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    lemma_map_ext_equal(m1, m2);
}

pub broadcast proof fn lemma_imap_ext_equal<K, V>(m1: IMap<K, V>, m2: IMap<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    super::gmap::lemma_map_ext_equal(m1.to_gmap(), m2.to_gmap());
    lemma_imap_dom_bridge(m1);
    lemma_imap_dom_bridge(m2);
    if m1 =~= m2 {
        assert(m1.to_gmap() =~= m2.to_gmap());
        assert(m1.to_gmap().dom() =~= m2.to_gmap().dom());
        assert forall|k: K| m1.dom().contains(k) == m2.dom().contains(k) by {
            assert(m1.dom().to_gset().contains(k) == m1.to_gmap().dom().contains(k));
            assert(m2.dom().to_gset().contains(k) == m2.to_gmap().dom().contains(k));
        }
        super::iset::lemma_iset_ext_equal(m1.dom(), m2.dom());
        assert forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k] by {
            if m1.dom().contains(k) {
                lemma_imap_dom_contains_bridge(m1, k);
                lemma_imap_dom_contains_bridge(m2, k);
                assert(m1.to_gmap().dom().contains(k) == m1.dom().contains(k));
                assert(m1.to_gmap().dom().contains(k));
                assert(m1.to_gmap().dom().contains(k) == m2.to_gmap().dom().contains(k));
                assert(m2.to_gmap().dom().contains(k));
                assert(m1.to_gmap()[k] == m2.to_gmap()[k]);
                assert(m1[k] == m1.to_gmap()[k]);
                assert(m2[k] == m2.to_gmap()[k]);
            }
        }
    }
    if ({
        &&& m1.dom() =~= m2.dom()
        &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
    }) {
        super::iset::lemma_iset_ext_equal(m1.dom(), m2.dom());
        assert forall|k: K| m1.to_gmap().dom().contains(k) == m2.to_gmap().dom().contains(k) by {
            assert(m1.dom().to_gset().contains(k) == m1.to_gmap().dom().contains(k));
            assert(m2.dom().to_gset().contains(k) == m2.to_gmap().dom().contains(k));
            assert(m1.dom().contains(k) == m2.dom().contains(k));
        }
        super::gset::lemma_gset_ext_equal(m1.to_gmap().dom(), m2.to_gmap().dom());
        assert forall|k: K| #![auto] m1.to_gmap().dom().contains(k) ==> m1.to_gmap()[k] == m2.to_gmap()[k] by {
            if m1.to_gmap().dom().contains(k) {
                lemma_imap_dom_contains_bridge(m1, k);
                lemma_imap_dom_contains_bridge(m2, k);
                assert(m1.to_gmap().dom().contains(k) == m1.dom().contains(k));
                assert(m1.dom().contains(k));
                assert(m1[k] == m2[k]);
                assert(m1[k] == m1.to_gmap()[k]);
                assert(m2[k] == m2.to_gmap()[k]);
            }
        }
        assert(m1.to_gmap() =~= m2.to_gmap());
        assert(m1 =~= m2);
    }
}

pub broadcast proof fn lemma_imap_ext_equal_eq<K, V>(m1: IMap<K, V>, m2: IMap<K, V>)
    ensures
        #[trigger] (m1 =~= m2) ==> m1 == m2,
{
    if m1 =~= m2 {
        super::gmap::lemma_map_ext_equal_eq(m1.to_gmap(), m2.to_gmap());
        assert(m1.to_gmap() == m2.to_gmap());
        assert(m1 == m2);
    }
}

pub broadcast proof fn lemma_imap_equal_implies_ext_equal<K, V>(m1: IMap<K, V>, m2: IMap<K, V>)
    ensures
        #![trigger m1.to_gmap(), m2.to_gmap()]
        m1 == m2 ==> m1 =~= m2,
{
    if m1 == m2 {
        assert(m1.to_gmap() == m2.to_gmap());
        assert(m1.to_gmap() =~= m2.to_gmap());
        assert(m1 =~= m2);
    }
}

pub broadcast proof fn lemma_imap_ext_equal_contains_value<K, V>(m1: IMap<K, V>, m2: IMap<K, V>, v: V)
    requires
        m1 =~= m2,
    ensures
        #[trigger] m1.contains_value(v) <==> #[trigger] m2.contains_value(v),
{
    lemma_imap_ext_equal(m1, m2);
    if m1.contains_value(v) {
        lemma_imap_contains_value_witness(m1, v);
        let k = choose|k: K| #[trigger] m1.dom().contains(k) && m1[k] == v;
        lemma_imap_dom_contains_bridge(m2, k);
        lemma_imap_index_field_bridge(m2, k);
        assert(m2.dom().contains(k));
        assert(m2[k] == v);
        assert(m2.to_gmap().dom().contains(k));
        assert(m2.to_gmap()[k] == v);
        assert(exists|k2: K| #[trigger] m2.to_gmap().dom().contains(k2) && m2.to_gmap()[k2] == v);
        assert(m2.contains_value(v));
    }
    if m2.contains_value(v) {
        lemma_imap_contains_value_witness(m2, v);
        let k = choose|k: K| #[trigger] m2.dom().contains(k) && m2[k] == v;
        lemma_imap_dom_contains_bridge(m1, k);
        lemma_imap_index_field_bridge(m1, k);
        assert(m1.dom().contains(k));
        assert(m1[k] == v);
        assert(m1.to_gmap().dom().contains(k));
        assert(m1.to_gmap()[k] == v);
        assert(exists|k2: K| #[trigger] m1.to_gmap().dom().contains(k2) && m1.to_gmap()[k2] == v);
        assert(m1.contains_value(v));
    }
}

pub broadcast proof fn lemma_imap_ext_equal_values_contains<K, V>(m1: IMap<K, V>, m2: IMap<K, V>, v: V)
    requires
        m1 =~= m2,
    ensures
        #[trigger] m1.values().contains(v) <==> #[trigger] m2.values().contains(v),
{
    lemma_imap_values_contains(m1, v);
    lemma_imap_values_contains(m2, v);
    lemma_imap_ext_equal_contains_value(m1, m2, v);
}

pub broadcast proof fn lemma_congruence_extensionality<K, V, FINITE: Finiteness>(
    x: GenericMap<K, V, FINITE>,
    y: GenericMap<K, V, FINITE>,
)
    requires
        #[trigger] x.congruent(y),
    ensures
        x == y,
{
    super::gmap::lemma_congruence_extensionality(x, y);
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V, M: MapLike<K, V>>(m: M) -> M {
    m
}

pub(crate) broadcast group group_map_internal_axioms {
    lemma_map_to_from_gmap,
    lemma_imap_to_from_gmap,
    super::gmap::lemma_new_from_set_ensures,
    super::gmap::lemma_infinite_new_ensures,
    super::gmap::lemma_map_empty,
    super::gmap::lemma_map_insert_domain,
    super::gmap::lemma_map_insert_same,
    super::gmap::lemma_map_insert_different,
    super::gmap::lemma_map_remove_domain,
    super::gmap::lemma_map_remove_different,
    super::gmap::lemma_map_ext_equal,
    super::gmap::lemma_map_ext_equal_eq,
    super::gmap::lemma_map_ext_equal_deep,
    super::gmap::GMap::lemma_remove_keys,
    super::gmap::GMap::lemma_invert_ensures,
    super::gmap::GMap::lemma_restrict,
    super::gmap::GMap::lemma_map_entries,
    super::gmap::GMap::lemma_map_values_ensures,
    super::gmap::GMap::lemma_union_prefer_right,
    super::gmap::lemma_congruence_extensionality,
}

pub broadcast group group_map_axioms {
    lemma_infinite_new_ensures,
    lemma_map_from_to_gmap,
    lemma_imap_from_to_gmap,
    axiom_map_index_decreases_finite,
    axiom_map_index_decreases_infinite,
    lemma_map_empty,
    lemma_imap_empty,
    lemma_map_insert_domain,
    lemma_map_insert_same,
    lemma_map_insert_different,
    lemma_map_remove_domain,
    lemma_map_remove_different,
    lemma_map_remove_keys_contains_key,
    lemma_map_contains_pair,
    lemma_map_values_contains,
    lemma_map_insert_values_contains_other,
    lemma_map_insert_remove_values_contains_other,
    lemma_map_ext_equal,
    lemma_map_ext_equal_eq,
    lemma_map_ext_equal_deep,
    lemma_imap_contains_key_dom,
    lemma_imap_contains_key_implies_dom,
    lemma_imap_dom_implies_contains_key,
    lemma_imap_contains_pair,
    lemma_imap_values_contains,
    lemma_imap_remove_absent,
    lemma_imap_remove_keys_contains_key,
    lemma_imap_contains_value_witness,
    lemma_finite_new_ensures,
    lemma_imap_equal_implies_ext_equal,
    lemma_imap_ext_equal,
    lemma_imap_ext_equal_eq,
    lemma_imap_ext_equal_contains_value,
    lemma_imap_ext_equal_values_contains,
    lemma_congruence_extensionality,
}

} // verus!
