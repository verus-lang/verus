use super::map::Map;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::set_lib::*;

verus! {

broadcast use super::map::group_map_axioms, super::set::group_set_axioms;

impl<K, V> Map<K, V> {
    /// Is `true` if called by a "full" map, i.e., a map containing every element of type `A`.
    #[verifier::inline]
    pub open spec fn is_full(self) -> bool {
        self.dom().is_full()
    }

    /// Is `true` if called by an "empty" map, i.e., a map containing no elements and has length 0
    #[verifier::inline]
    pub open spec fn is_empty(self) -> (b: bool) {
        self.dom().is_empty()
    }

    /// Returns true if the key `k` is in the domain of `self`.
    #[verifier::inline]
    pub open spec fn contains_key(self, k: K) -> bool {
        self.dom().contains(k)
    }

    /// Returns true if the value `v` is in the range of `self`.
    pub open spec fn contains_value(self, v: V) -> bool {
        exists|i: K| #[trigger] self.dom().contains(i) && self[i] == v
    }

    ///
    /// Returns the set of values in the map.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].values() =~= set![10, 11]
    /// );
    /// ```
    pub open spec fn values(self) -> Set<V> {
        Set::<V>::new(|v: V| self.contains_value(v))
    }

    /// Returns true if the key `k` is in the domain of `self`, and it maps to the value `v`.
    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && self[k] == v
    }

    /// Returns true if `m1` is _contained in_ `m2`, i.e., the domain of `m1` is a subset
    /// of the domain of `m2`, and they agree on all values in `m1`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert(
    ///    map![1 => 10, 2 => 11].le(map![1 => 10, 2 => 11, 3 => 12])
    /// );
    /// ```
    pub open spec fn submap_of(self, m2: Self) -> bool {
        forall|k: K| #[trigger]
            self.dom().contains(k) ==> #[trigger] m2.dom().contains(k) && self[k] == m2[k]
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, m2: Self) -> bool {
        self.submap_of(m2)
    }

    /// Deprecated synonym for `submap_of`
    #[verifier::inline]
    #[cfg_attr(not(verus_verify_core), deprecated = "use m1.submap_of(m2) or m1 <= m2 instead")]
    pub open spec fn le(self, m2: Self) -> bool {
        self.submap_of(m2)
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
    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) || m2.dom().contains(k),
            |k: K|
                if m2.dom().contains(k) {
                    m2[k]
                } else {
                    self[k]
                },
        )
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
    pub open spec fn remove_keys(self, keys: Set<K>) -> Self {
        Self::new(|k: K| self.dom().contains(k) && !keys.contains(k), |k: K| self[k])
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
    pub open spec fn restrict(self, keys: Set<K>) -> Self {
        Self::new(|k: K| self.dom().contains(k) && keys.contains(k), |k: K| self[k])
    }

    /// Returns `true` if and only if the given key maps to the same value or does not exist in self and m2.
    pub open spec fn is_equal_on_key(self, m2: Self, key: K) -> bool {
        ||| (!self.dom().contains(key) && !m2.dom().contains(key))
        ||| (self.dom().contains(key) && m2.dom().contains(key) && self[key] == m2[key])
    }

    /// Returns `true` if the two given maps agree on all keys that their domains share
    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==> self[k] == m2[k]
    }

    /// Map a function `f` over all (k, v) pairs in `self`.
    pub open spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(k, self[k]))
    }

    /// Map a function `f` over the values in `self`.
    pub open spec fn map_values<W>(self, f: spec_fn(V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(self[k]))
    }

    /// Returns `true` if and only if a map is injective
    pub open spec fn is_injective(self) -> bool {
        forall|x: K, y: K|
            x != y && self.dom().contains(x) && self.dom().contains(y) ==> #[trigger] self[x]
                != #[trigger] self[y]
    }

    /// Swaps map keys and values. Values are not required to be unique; no
    /// promises on which key is chosen on the intersection.
    pub open spec fn invert(self) -> Map<V, K> {
        Map::<V, K>::new(
            |v: V| self.contains_value(v),
            |v: V| choose|k: K| self.contains_pair(k, v),
        )
    }

    // Proven lemmas
    /// Removing a key from a map that previously contained that key decreases
    /// the map's length by one
    pub proof fn lemma_remove_key_len(self, key: K)
        requires
            self.dom().contains(key),
            self.dom().finite(),
        ensures
            self.dom().len() == 1 + self.remove(key).dom().len(),
    {
    }

    /// The domain of a map after removing a key is equivalent to removing the key from
    /// the domain of the original map.
    pub proof fn lemma_remove_equivalency(self, key: K)
        ensures
            self.remove(key).dom() == self.dom().remove(key),
    {
    }

    /// Removing a set of n keys from a map that previously contained all n keys
    /// results in a domain of size n less than the original domain.
    pub proof fn lemma_remove_keys_len(self, keys: Set<K>)
        requires
            forall|k: K| #[trigger] keys.contains(k) ==> self.contains_key(k),
            keys.finite(),
            self.dom().finite(),
        ensures
            self.remove_keys(keys).dom().len() == self.dom().len() - keys.len(),
        decreases keys.len(),
    {
        lemma_set_properties::<K>();
        if keys.len() > 0 {
            let key = keys.choose();
            let val = self[key];
            self.remove(key).lemma_remove_keys_len(keys.remove(key));
            assert(self.remove(key).remove_keys(keys.remove(key)) =~= self.remove_keys(keys));
        } else {
            assert(self.remove_keys(keys) =~= self);
        }
    }

    /// The function `invert` results in an injective map
    pub proof fn lemma_invert_is_injective(self)
        ensures
            self.invert().is_injective(),
    {
        assert forall|x: V, y: V|
            x != y && self.invert().dom().contains(x) && self.invert().dom().contains(
                y,
            ) implies #[trigger] self.invert()[x] != #[trigger] self.invert()[y] by {
            let i = choose|i: K| #[trigger] self.dom().contains(i) && self[i] == x;
            assert(self.contains_pair(i, x));
            let j = choose|j: K| self.contains_pair(j, x) && self.invert()[x] == j;
            let k = choose|k: K| #[trigger] self.dom().contains(k) && self[k] == y;
            assert(self.contains_pair(k, y));
            let l = choose|l: K| self.contains_pair(l, y) && self.invert()[y] == l && l != j;
        }
    }
}

impl Map<int, int> {
    /// Returns `true` if a map is monotonic -- that is, if the mapping between ordered sets
    /// preserves the regular `<=` ordering on integers.
    pub open spec fn is_monotonic(self) -> bool {
        forall|x: int, y: int|
            self.dom().contains(x) && self.dom().contains(y) && x <= y ==> #[trigger] self[x]
                <= #[trigger] self[y]
    }

    /// Returns `true` if and only if a map is monotonic, only considering keys greater than
    /// or equal to start
    pub open spec fn is_monotonic_from(self, start: int) -> bool {
        forall|x: int, y: int|
            self.dom().contains(x) && self.dom().contains(y) && start <= x <= y
                ==> #[trigger] self[x] <= #[trigger] self[y]
    }
}

// Proven lemmas
/// The size of the union of two disjoint maps is equal to the sum of the sizes of the individual maps
pub proof fn lemma_disjoint_union_size<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.dom().disjoint(m2.dom()),
        m1.dom().finite(),
        m2.dom().finite(),
    ensures
        m1.union_prefer_right(m2).dom().len() == m1.dom().len() + m2.dom().len(),
{
    let u = m1.union_prefer_right(m2);
    assert(u.dom() =~= m1.dom() + m2.dom());  //proves u.dom() is finite
    assert(u.remove_keys(m1.dom()).dom() =~= m2.dom());
    assert(u.remove_keys(m1.dom()).dom().len() == u.dom().len() - m1.dom().len()) by {
        u.lemma_remove_keys_len(m1.dom());
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The domain of a map constructed with `Map::new(fk, fv)` is equivalent to the set constructed with `Set::new(fk)`.
pub proof fn lemma_map_new_domain<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),
{
    assert(Set::new(fk) =~= Set::<K>::new(|k: K| fk(k)));
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The set of values of a map constructed with `Map::new(fk, fv)` is equivalent to
/// the set constructed with `Set::new(|v: V| (exists |k: K| fk(k) && fv(k) == v)`. In other words,
/// the set of all values fv(k) where fk(k) is true.
pub proof fn lemma_map_new_values<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
            |v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),
        ),
{
    let keys = Set::<K>::new(fk);
    let values = Map::<K, V>::new(fk, fv).values();
    let map = Map::<K, V>::new(fk, fv);
    assert(map.dom() =~= keys);
    assert(forall|k: K| #[trigger] fk(k) ==> keys.contains(k));
    assert(values =~= Set::<V>::new(
        |v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),
    ));
}

/// Properties of maps from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_map_properties<K, V>()
    ensures
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),  //from lemma_map_new_domain
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
                |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
            ),  //from lemma_map_new_values
{
    assert forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
        Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)) by {
        lemma_map_new_domain(fk, fv);
    }
    assert forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
        Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
            |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
        ) by {
        lemma_map_new_values(fk, fv);
    }
}

pub proof fn lemma_values_finite<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
    ensures
        m.values().finite(),
    decreases m.len(),
{
    if m.len() > 0 {
        let k = m.dom().choose();
        let v = m[k];
        let m1 = m.remove(k);
        assert(m.contains_key(k));
        assert(m.contains_value(v));
        let mv = m.values();
        let m1v = m1.values();
        assert_sets_equal!(mv == m1v.insert(v), v0 => {
            if m.contains_value(v0) {
                if v0 != v {
                    let k0 = choose|k0| #![auto] m.contains_key(k0) && m[k0] == v0;
                    assert(k0 != k);
                    assert(m1.contains_key(k0));
                    assert(mv.contains(v0) ==> m1v.insert(v).contains(v0));
                    assert(mv.contains(v0) <== m1v.insert(v).contains(v0));
                }
            }
        });
        assert(m1.len() < m.len());
        lemma_values_finite(m1);
        axiom_set_insert_finite(m1.values(), v);
    } else {
        assert(m.values() =~= Set::<V>::empty());
    }
}

} // verus!
