#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;
use super::set::*;

verus! {

/// `Map<K, V>` is an abstract map type for specifications.
/// To use a "map" in compiled code, use an `exec` type like HashMap (TODO)
/// that has a `Map<K, V>` as its specification type.
///
/// An object `map: Map<K, V>` has a _domain_, a set of keys given by [`map.dom()`](Map::dom),
/// and a mapping for keys in the domain to values, given by [`map[key]`](Map::index).
/// Alternatively, a map can be thought of as a set of `(K, V)` pairs where each key
/// appears in at most entry.
///
/// Map allows only construction of maps with finite domain.
/// The IMap type allows possibly-infinite domains.
/// The [`self.finite()`](Set::finite) predicate can indicate (at verification time) whether a
/// specific IMap has a finite domain.
///
/// Maps can be constructed in a few different ways:
///  * [`Map::empty()`] constructs an empty map.
///  * [`Map::new`] and [`Map::total`] construct a map given functions that specify its domain and the mapping
///     from keys to values (a _map comprehension_).
///  * The [`map!`] macro, to construct small maps of a fixed size.
///  * By manipulating an existing map with [`Map::insert`] or [`Map::remove`].
///
/// To prove that two maps are equal, it is usually easiest to use the extensionality operator `=~=`.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct GMap<K, V, FINITE: Finiteness> {
    mapping: spec_fn(K) -> Option<V>,
    _phantom: core::marker::PhantomData<FINITE>,
}

/// Map<K,V> is a type synonym for map whose membership is finite (known at typechecking time).
pub type Map<K, V> = GMap<K, V, Finite>;

pub broadcast proof fn lemma_map_finite_from_type<K, V>(m: Map<K, V>)
    ensures
        #[trigger] m.dom().finite(),
{
    admit();
}

impl<K, V, FINITE: Finiteness> GMap<K, V, FINITE> {
    /// Returns true if the key `k` is in the domain of `self`.
    #[verifier::inline]
    pub open spec fn contains_key(self, k: K) -> bool {
        self.dom().contains(k)
    }

    /// Returns true if the value `v` is in the range of `self`.
    pub open spec fn contains_value(self, v: V) -> bool {
        exists|i: K| #[trigger] self.dom().contains(i) && self[i] == v
    }

    /// Returns true if the key `k` is in the domain of `self`, and it maps to the value `v`.
    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && self[k] == v
    }

    pub open spec fn congruent<FINITE2: Finiteness>(
        self: GMap<K, V, FINITE>,
        m2: GMap<K, V, FINITE2>,
    ) -> bool {
        &&& self.dom().congruent(m2.dom())
        &&& forall|k| #[trigger] self.contains_key(k) ==> self[k] == m2[k]
    }

    pub open spec fn to_infinite(self) -> IMap<K, V> {
        IMap::new(|k| self.contains_key(k), |k| self[k])
    }

    pub open spec fn to_finite(self) -> Map<K, V>
        recommends
            self.dom().finite(),
    {
        Map::new(self.dom().to_finite(), |k| self[k])
    }
}

/// IMap<K,V> is a type synonym a set whose membership may be infinite (but can be
/// proven finite at verification time).
pub type IMap<K, V> = GMap<K, V, Infinite>;

impl<K, V, FINITE: Finiteness> GMap<K, V, FINITE> {
    /// An empty map.
    pub closed spec fn empty() -> Self {
        GMap { mapping: |k| None, _phantom: core::marker::PhantomData }
    }

    /// The domain of the map as a set.
    pub closed spec fn dom(self) -> GSet<K, FINITE> {
        ISet::new(|k| (self.mapping)(k) is Some).cast_finiteness()
    }

    /// Gets the value that the given key `key` maps to.
    /// For keys not in the domain, the result is meaningless and arbitrary.
    pub closed spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        (self.mapping)(key)->Some_0
    }

    /// `[]` operator, synonymous with `index`
    #[verifier::inline]
    pub open spec fn spec_index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    {
        self.index(key)
    }

    /// Inserts the given (key, value) pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.
    pub closed spec fn insert(self, key: K, value: V) -> Self {
        GMap {
            mapping: |k|
                if k == key {
                    Some(value)
                } else {
                    (self.mapping)(k)
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Removes the given key and its associated value from the map.
    ///
    /// If the key is already absent from the map, then the map is left unchanged.
    pub closed spec fn remove(self, key: K) -> Self {
        GMap {
            mapping: |k|
                if k == key {
                    None
                } else {
                    (self.mapping)(k)
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Returns the number of key-value pairs in the map
    pub open spec fn len(self) -> nat {
        self.dom().len()
    }

    /// Gives the union of two maps, defined as:
    ///  * The domain is the union of the two input maps.
    ///  * For a given key in _both_ input maps, it maps to the same value that it maps to in the _right_ map (`m2`).
    ///  * For any other key in either input map (but not both), it maps to the same value
    ///    as it does in that map.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].union_prefer_right(map![1 => 20, 3 => 13])
    ///    =~= map![1 => 20, 2 => 11, 3 => 13]);
    /// ```
    // Someday it might be nice to generalize union_prefer_right (and tracked_union_prefer_right)
    // to accept arbitrary FINITEnesses, and then provide specialized versions that preserve
    // FINITE=true when both args are FINITE=true, as is done with GSet::union.
    // We'll worry about this someday when some user level code actually cares to jump over the
    // divide.
    pub closed spec fn union_prefer_right(self, m2: Self) -> Self {
        Self {
            mapping: |k: K|
                if self.dom().contains(k) || m2.dom().contains(k) {
                    Some(
                        if m2.dom().contains(k) {
                            m2[k]
                        } else {
                            self[k]
                        },
                    )
                } else {
                    None
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Removes the given keys and their associated values from the map.
    ///
    /// Ignores any key in `keys` which is not in the domain of `self`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4})
    ///    =~= map![1 => 10]);
    /// ```
    pub closed spec fn remove_keys(self, keys: GSet<K, FINITE>) -> Self {
        Self {
            mapping: |k: K|
                if self.dom().contains(k) && !keys.contains(k) {
                    Some(self[k])
                } else {
                    None
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Complement to `remove_keys`. Restricts the map to (key, value) pairs
    /// for keys that are _in_ the given set; that is, it removes any keys
    /// _not_ in the set.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4})
    ///    =~= map![2 => 11, 3 => 12]);
    /// ```
    pub closed spec fn restrict(self, keys: GSet<K, FINITE>) -> Self {
        Self {
            mapping: |k: K|
                if self.dom().contains(k) && keys.contains(k) {
                    Some(self[k])
                } else {
                    None
                },
            _phantom: core::marker::PhantomData,
        }
    }

    // DONE(jonh): expose as broadcast lemmas
    // okay, good, actually the problem was a missing trigger
    pub broadcast proof fn lemma_union_prefer_right(self, m2: Self)
        ensures
            #![trigger (self.union_prefer_right(m2))]
            self.union_prefer_right(m2).dom().to_infinite() == self.dom().generic_union(m2.dom()),
            self.union_prefer_right(m2).dom().congruent(self.dom().generic_union(m2.dom())),
            forall|k|
                #![auto]
                self.union_prefer_right(m2).dom().contains(k) ==> self.union_prefer_right(m2)[k]
                    == if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;

        assert(self.union_prefer_right(m2).dom().to_infinite() == self.dom().generic_union(
            m2.dom(),
        ));
    }

    pub broadcast proof fn lemma_remove_keys(self, keys: GSet<K, FINITE>)
        ensures
            #![trigger(self.remove_keys(keys))]
            self.remove_keys(keys).dom().to_infinite() == self.dom().generic_difference(keys),
            self.remove_keys(keys).dom().congruent(self.dom().generic_difference(keys)),
            // TODO(jonh): ask Chris if there's a better trigger here.
            // Things got ugly in verus-mimalloc/os_mem_util::split
            forall|k|
                #![auto]
                self.remove_keys(keys).dom().contains(k) ==> self.remove_keys(keys)[k] == self[k],
            forall|k|
                #![auto]
                self.dom().contains(k) && !keys.contains(k) ==> self.remove_keys(keys)[k]
                    == self[k],
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn

        assert(self.remove_keys(keys).dom().to_infinite() == self.dom().generic_difference(keys));
    }

    pub broadcast proof fn lemma_restrict(self, keys: GSet<K, FINITE>)
        ensures
            #![trigger(self.restrict(keys))]
            self.restrict(keys).dom().to_infinite() == self.dom().generic_intersect(keys),
            self.restrict(keys).dom().congruent(self.dom().generic_intersect(keys)),
            forall|k|
                #![auto]
                self.restrict(keys).dom().contains(k) ==> self.restrict(keys)[k] == self[k],
            forall|k|
                #![auto]
                self.dom().contains(k) && keys.contains(k) ==> self.restrict(keys)[k] == self[k],
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn

        assert(self.restrict(keys).dom().to_infinite() == self.dom().generic_intersect(keys));
    }

    // Preserves finite soundness because, when FINITE=Finite, key_set is finite by its type.
    pub closed spec fn from_set(key_set: GSet<K, FINITE>, fv: spec_fn(K) -> V) -> GMap<
        K,
        V,
        FINITE,
    > {
        GMap {
            mapping: |k|
                if key_set.contains(k) {
                    Some(fv(k))
                } else {
                    None
                },
            _phantom: core::marker::PhantomData,
        }
    }

    /// Map a function `f` over all (k, v) pairs in `self`.
    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> GMap<K, W, FINITE> {
        GMap::from_set(self.dom(), |k| f(k, self[k]))
    }

    pub broadcast proof fn lemma_map_entries<W>(self, f: spec_fn(K, V) -> W)
        ensures
            #![trigger(self.map_entries(f))]
            self.map_entries(f).dom() == self.dom(),
            forall|k|
                #![auto]
                self.map_entries(f).contains_key(k) ==> self.map_entries(f)[k] == f(k, self[k]),
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn

        assert(self.map_entries(f).dom() == self.dom());
    }

    /// Map a function `f` over the values in `self`.
    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> GMap<K, W, FINITE> {
        GMap::from_set(self.dom(), |k| f(self[k]))
    }

    pub broadcast proof fn lemma_map_values_ensures<W>(self, f: spec_fn(V) -> W)
        ensures
            #![trigger(self.map_values(f))]
            self.dom() == self.map_values(f).dom(),
            forall|k| #[trigger]
                self.map_values(f).dom().contains(k) ==> self.map_values(f)[k] == f(self[k]),
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;

        assert(self.dom() =~= self.map_values(f).dom());  // trigger-it-yourself
    }

    /// Swaps map keys and values. Values are not required to be unique; no
    /// promises on which key is chosen on the intersection.
    pub open spec fn invert(self) -> GMap<V, K, FINITE> {
        GMap::from_set(self.dom().map(|k| self[k]), |v| choose|k: K| self.contains_pair(k, v))
    }

    /// Export publicly-meaningful definition of invert
    pub broadcast proof fn lemma_invert_ensures(self)
        ensures
            #![trigger(self.invert())]
            GMap::congruent(
                self.invert(),
                IMap::new(|v| self.contains_value(v), |v| choose|k: K| self.contains_pair(k, v)),
            ),
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;

    }
}

impl<K, V, FINITE: Finiteness> GMap<K, V, FINITE> {
    pub axiom fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == GMap::<K, V, FINITE>::empty(),
    ;

    pub axiom fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == Self::insert(*old(self), key, value),
    ;

    /// todo fill in documentation
    pub axiom fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == Self::remove(*old(self), key),
            v == old(self)[key],
    ;

    pub axiom fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    ;

    // Note this soundly preserves finiteness because it is doing set
    // mapping, which preserves finiteness.
    #[verifier::external_body]
    pub axiom fn tracked_map_keys<J>(
        tracked old_map: Map<K, V>,
        key_map: Map<J, K>,
    ) -> (tracked new_map: Map<J, V>)
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old_map.dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                !equal(j1, j2) && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> !equal(key_map.index(j1), key_map.index(j2)),
        ensures
            forall|j| #[trigger] new_map.dom().contains(j) <==> key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> new_map.dom().contains(j) && #[trigger] new_map.index(
                    j,
                ) == old_map.index(key_map.index(j)),
    ;

    pub axiom fn tracked_remove_keys(tracked &mut self, keys: GSet<K, FINITE>) -> (tracked out_map:
        Self)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    ;

    pub axiom fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    ;

    #[verifier::external_body]
    pub proof fn tracked_to_finite(tracked self) -> (tracked out: Map<K, V>)
        requires
            self.dom().finite(),
        ensures
            self.congruent(out),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_to_infinite(tracked self) -> (tracked out: IMap<K, V>)
        ensures
            self.congruent(out),
    {
        unimplemented!();
    }
}

broadcast proof fn axiom_dom_ensures<K, V, FINITE: Finiteness>(m: GMap<K, V, FINITE>)
    ensures
        (#[trigger] m.dom()).congruent(ISet::new(|k| (m.mapping)(k) is Some)),
{
    // This property relies on this module only allowing the construction of
    // finite mappings inside GMaps with FINITE=true.
    admit();
}

impl<K, V> Map<K, V> {
    #[verifier::inline]
    pub open spec fn new(key_set: Set<K>, fv: spec_fn(K) -> V) -> Map<K, V> {
        Map::from_set(key_set, fv)
    }
}

pub broadcast proof fn lemma_new_from_set_ensures<K, V, FINITE: Finiteness>(
    key_set: GSet<K, FINITE>,
    fv: spec_fn(K) -> V,
)
    ensures
        #![trigger(GMap::from_set(key_set, fv))]
        forall|k|
            key_set.contains(k) <==> #[trigger] GMap::from_set(key_set, fv).dom().contains(k),
        forall|k| key_set.contains(k) ==> #[trigger] GMap::from_set(key_set, fv)[k] == fv(k),
{
    broadcast use super::set::group_set_lemmas;
    broadcast use axiom_dom_ensures;

}

impl<K, V> IMap<K, V> {
    /// Gives an `IMap<K, V>` whose domain contains every key, and maps each key
    /// to the value given by `fv`.
    pub open spec fn total(fv: spec_fn(K) -> V) -> IMap<K, V> {
        IMap::new(|k| true, fv)
    }

    /// Gives a `IMap<K, V>` whose domain is given by the boolean predicate on keys `fk`,
    /// and maps each key to the value given by `fv`.
    pub closed spec fn new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V) -> IMap<K, V> {
        IMap {
            mapping: |k|
                if fk(k) {
                    Some(fv(k))
                } else {
                    None
                },
            _phantom: core::marker::PhantomData,
        }
    }
}

pub broadcast proof fn lemma_infinite_new_ensures<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #![trigger(IMap::new(fk, fv))]
        forall|k|
            #![auto]
            fk(k) <==> (#[trigger] IMap::new(fk, fv)).dom().contains(k),
        forall|k| #![auto] fk(k) ==> IMap::new(fk, fv)[k] == fv(k),
{
    broadcast use super::set::group_set_lemmas;
    broadcast use axiom_dom_ensures;

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
pub broadcast proof fn axiom_map_empty<K, V, FINITE: Finiteness>()
    ensures
        #[trigger] GMap::<K, V, FINITE>::empty().dom() == GSet::<K, FINITE>::empty(),
{
    broadcast use {super::set::group_set_lemmas, axiom_dom_ensures};

    assert(GMap::<K, V, FINITE>::empty().dom() == GSet::<K, FINITE>::empty());
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
pub broadcast proof fn axiom_map_insert_domain<K, V, FINITE: Finiteness>(
    m: GMap<K, V, FINITE>,
    key: K,
    value: V,
)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    broadcast use super::set::group_set_lemmas;
    broadcast use axiom_dom_ensures;
    //     m.axiom_dom_ensures();
    //     m.insert(key, value).axiom_dom_ensures();

    assert(m.insert(key, value).dom() =~= m.dom().insert(key));
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
pub broadcast proof fn axiom_map_insert_same<K, V, FINITE: Finiteness>(
    m: GMap<K, V, FINITE>,
    key: K,
    value: V,
)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
pub broadcast proof fn axiom_map_insert_different<K, V, FINITE: Finiteness>(
    m: GMap<K, V, FINITE>,
    key1: K,
    key2: K,
    value: V,
)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
pub broadcast proof fn axiom_map_remove_domain<K, V, FINITE: Finiteness>(
    m: GMap<K, V, FINITE>,
    key: K,
)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    broadcast use super::set::group_set_lemmas;
    broadcast use axiom_dom_ensures;
    //     m.axiom_dom_ensures();
    //     m.remove(key).axiom_dom_ensures();

    assert(m.remove(key).dom() =~= m.dom().remove(key));
}

/// Removing a key-value pair from a map does not change the value mapped to by
/// any other keys in the map.
pub broadcast proof fn axiom_map_remove_different<K, V, FINITE: Finiteness>(
    m: GMap<K, V, FINITE>,
    key1: K,
    key2: K,
)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
pub broadcast proof fn axiom_map_ext_equal<K, V, FINITE: Finiteness>(
    m1: GMap<K, V, FINITE>,
    m2: GMap<K, V, FINITE>,
)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    broadcast use axiom_dom_ensures;
    //     m1.axiom_dom_ensures();
    //     m2.axiom_dom_ensures();
    broadcast use super::set::group_set_lemmas;

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
        }
        assert(m1 =~= m2);
    }
}

pub broadcast proof fn axiom_map_ext_equal_deep<K, V, FINITE: Finiteness>(
    m1: GMap<K, V, FINITE>,
    m2: GMap<K, V, FINITE>,
)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    axiom_map_ext_equal(m1, m2);
}

pub broadcast group group_map_axioms {
    lemma_new_from_set_ensures,
    lemma_infinite_new_ensures,
    GMap::lemma_remove_keys,
    GMap::lemma_invert_ensures,
    GMap::lemma_restrict,
    GMap::lemma_map_entries,
    GMap::lemma_map_values_ensures,
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
    GMap::lemma_union_prefer_right,
    //     lemma_union_prefer_right_noself,
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

/// Create a finite Map using syntax like `map![key1 => val1, key2 => val, ...]`.
///
/// This is equivalent to `Map::empty().insert(key1, val1).insert(key2, val2)...`.
///
/// Note that this does _not_ require all keys to be distinct. In the case that two
/// or more keys are equal, the resulting map uses the value of the rightmost entry.
#[macro_export]
macro_rules! map {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::vstd::map::map_internal!($($tail)*))
    };
}

/// Create an IMap using syntax like `map![key1 => val1, key2 => val, ...]`.
///
/// This is equivalent to `Map::empty().insert(key1, val1).insert(key2, val2)...`.
///
/// Note that this does _not_ require all keys to be distinct. In the case that two
/// or more keys are equal, the resulting map uses the value of the rightmost entry.
#[doc(hidden)]
#[macro_export]
macro_rules! imap_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::map::IMap::empty()
            $(.insert($key, $value))*
    }
}

#[macro_export]
macro_rules! imap {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::map::imap_internal!($($tail)*))
    };
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V, FINITE: Finiteness>(m: GMap<K, V, FINITE>) -> GMap<
    K,
    V,
    FINITE,
> {
    m
}

#[doc(hidden)]
pub use map_internal;
pub use map;
#[doc(hidden)]
pub use imap_internal;
pub use imap;

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
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::vstd::map::assert_maps_equal_internal!($($tail)*))
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
        ::verus_builtin::assert_by(::verus_builtin::equal(m1, m2), {
            ::verus_builtin::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                ::verus_builtin::ensures([
                    ::verus_builtin::imply(#[verifier::trigger] m1.dom().contains($k), m2.dom().contains($k))
                    && ::verus_builtin::imply(m2.dom().contains($k), m1.dom().contains($k))
                    && ::verus_builtin::imply(m1.dom().contains($k) && m2.dom().contains($k),
                        ::verus_builtin::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            ::verus_builtin::assert_(::verus_builtin::ext_equal(m1, m2));
        });
    }
}

#[doc(hidden)]
pub use assert_maps_equal_internal;
pub use assert_maps_equal;

impl<K, V> Map<K, V> {
    pub proof fn tracked_map_keys_in_place(
        #[verifier::proof]
        &mut self,
        key_map: Map<K, K>,
    )
        requires
            forall|j|
                #![auto]
                key_map.dom().contains(j) ==> old(self).dom().contains(key_map.index(j)),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                    ==> key_map.index(j1) != key_map.index(j2),
        ensures
            forall|j| #[trigger] self.dom().contains(j) == key_map.dom().contains(j),
            forall|j|
                key_map.dom().contains(j) ==> self.dom().contains(j) && #[trigger] self.index(j)
                    == old(self).index(key_map.index(j)),
    {
        #[verifier::proof]
        let mut tmp = Self::tracked_empty();
        super::modes::tracked_swap(&mut tmp, self);
        #[verifier::proof]
        let mut tmp = Self::tracked_map_keys(tmp, key_map);
        super::modes::tracked_swap(&mut tmp, self);
    }
}

} // verus!
