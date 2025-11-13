#[macro_use]
use super::map::{Map, assert_maps_equal, assert_maps_equal_internal};
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::set_lib::*;

verus! {

broadcast use {super::map::group_map_axioms, super::set::group_set_axioms};

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

    /// Returns `Some(v)` if the key `k` is in the domain of `self` and maps to `v`,
    /// and `None` if the key `k` is not in the domain of `self`.
    pub open spec fn index_opt(self, k: K) -> Option<V> {
        if self.contains_key(k) {
            Some(self[k])
        } else {
            None
        }
    }

    ///
    /// Returns the set of values in the map.
    ///
    /// ## Example
    ///
    /// ```rust
    /// let m: Map<int, int> = map![1 => 10, 2 => 11];
    /// assert(m.values() == set![10int, 11int]) by {
    ///     assert(m.contains_key(1));
    ///     assert(m.contains_key(2));
    ///     assert(m.values() =~= set![10int, 11int]);
    /// }
    /// ```
    pub open spec fn values(self) -> Set<V> {
        Set::<V>::new(|v: V| self.contains_value(v))
    }

    ///
    /// Returns the set of key-value pairs representing the map
    ///
    /// ## Example
    ///
    /// ```rust
    /// let m: Map<int, int> = map![1 => 10, 2 => 11];
    /// assert(m.kv_pairs() == set![(1int, 10int), (2int, 11int)] by {
    ///     assert(m.contains_pair(1int, 10int));
    ///     assert(m.contains_pair(2int, 11int));
    ///     assert(m.kv_pairs() =~= set![(1int, 10int), (2int, 11int)]);
    /// }
    /// ```
    pub open spec fn kv_pairs(self) -> Set<(K, V)> {
        Set::<(K, V)>::new(|kv: (K, V)| self.dom().contains(kv.0) && self[kv.0] == kv.1)
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
        broadcast use group_set_properties;

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

    /// Keeps only those key-value pairs whose key satisfies `p`.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![1 => 10, 2 => 20];
    ///     let even = |k: int| k % 2 == 0;
    ///     assert(m.filter_keys(even) =~= map![2 => 20]);
    /// }
    /// ```
    pub open spec fn filter_keys(self, p: spec_fn(K) -> bool) -> Self {
        self.restrict(self.dom().filter(p))
    }

    /// Returns the value associated with key `k` in the map if it exists,
    /// otherwise returns None.
    ///
    /// ## Example
    /// ```rust
    /// proof fn get_test() {
    ///     let m: Map<int, bool> = map![
    ///         1 => true,
    ///         2 => false
    ///     ];
    ///
    ///     assert(m.get(1) == Some(true));
    ///     assert(m.get(3) == None);
    /// }
    /// ```
    pub open spec fn get(self, k: K) -> Option<V> {
        if self.dom().contains(k) {
            Some(self[k])
        } else {
            None
        }
    }

    /// A map contains a value satisfying predicate `p` iff some key maps to a value satisfying `p`.
    ///
    /// ## Example
    /// ```rust
    /// proof fn get_dom_value_any_test() {
    ///     let m = map![1 => 10, 2 => 20, 3 => 30];
    ///     let p = |v: int| v > 25;
    ///     assert(m[3] == 30);
    ///     assert(m.dom().any(|k| p(m[k])));
    /// }
    /// ```
    pub proof fn get_dom_value_any(self, p: spec_fn(V) -> bool)
        ensures
            self.dom().any(|k: K| p(self[k])) <==> self.values().any(p),
    {
        broadcast use group_map_properties;

        if self.dom().any(|k: K| p(self[k])) {
            let k = choose|k: K| self.dom().contains(k) && #[trigger] p(self[k]);
            assert(self.values().contains(self[k]));
            assert(self.values().any(p));
        }
    }

    /// Two maps are equal if and only if they are submaps of each other.
    ///
    /// ## Example
    /// ```rust
    /// proof fn submap_eq_test() {
    ///     let m1 = map![1 => 10, 2 => 20];
    ///     let m2 = map![1 => 10, 2 => 20];
    ///     let m3 = map![1 => 10, 2 => 30];
    ///
    ///     assert(m1.submap_of(m2) && m2.submap_of(m1));
    ///     assert(m1 == m2);
    /// }
    /// ```
    pub proof fn lemma_submap_eq_iff(self, m: Self)
        ensures
            (self == m) <==> (self.submap_of(m) && m.submap_of(self)),
    {
        broadcast use group_map_properties;

        if self.submap_of(m) && m.submap_of(self) {
            assert(self.dom() == m.dom());
            assert(self == m);
        }
    }

    /// When removing a set of keys from a map after inserting (k,v),
    /// the result depends on whether k is in the set:
    /// if k is in the set, the insertion is discarded;
    /// if not, the insertion happens after removal.
    ///
    /// ## Example
    /// ```rust
    /// proof fn map_remove_keys_insert_test() {
    ///     let m = map![1 => 10, 2 => 20, 3 => 30];
    ///     let to_remove = set![2, 4];
    ///
    ///     // 5 not in m: insert happens after remove
    ///     assert(m.insert(5, 15).remove_keys(to_remove) == m.remove_keys(to_remove).insert(5, 15));
    ///
    ///     // 2 in m: insert is eliminated by remove
    ///     assert(m.insert(2, 25).remove_keys(to_remove) == m.remove_keys(to_remove));
    /// }
    /// ```
    pub broadcast proof fn lemma_map_remove_keys_insert(self, r: Set<K>, k: K, v: V)
        ensures
            #[trigger] self.insert(k, v).remove_keys(r) == if r.contains(k) {
                self.remove_keys(r)
            } else {
                self.remove_keys(r).insert(k, v)
            },
    {
        broadcast use group_map_properties;

        let lhs = self.insert(k, v).remove_keys(r);
        let rhs = if r.contains(k) {
            self.remove_keys(r)
        } else {
            self.remove_keys(r).insert(k, v)
        };
        assert(lhs == rhs);
    }

    /// Filtering keys after inserting `(k, v)` leaves the result unchanged when `p(k)` is false,
    /// and otherwise adds `(k, v)` to the already-filtered map.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![1 => 10];
    ///     let even = |k: int| k % 2 == 0;
    ///
    ///     assert(m.insert(3, 30).filter_keys(even) =~= m.filter_keys(even));
    ///     assert(m.insert(2, 20).filter_keys(even)
    ///            =~= m.filter_keys(even).insert(2, 20));
    /// }
    /// ```
    pub broadcast proof fn lemma_filter_keys_insert(self, p: spec_fn(K) -> bool, k: K, v: V)
        ensures
            #[trigger] self.insert(k, v).filter_keys(p) == (if p(k) {
                self.filter_keys(p).insert(k, v)
            } else {
                self.filter_keys(p)
            }),
    {
        broadcast use group_map_properties;

        let lhs = self.insert(k, v).filter_keys(p);
        let rhs = if p(k) {
            self.filter_keys(p).insert(k, v)
        } else {
            self.filter_keys(p)
        };
        assert(lhs == rhs);
    }
}

impl<K, V> Map<Seq<K>, V> {
    /// Returns a sub-map of all entries whose key begins with `prefix`,
    /// re-indexed so that the stored keys have that prefix removed.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![seq![1, 2] => 10, seq![1, 2, 3] => 20, seq![2] => 30];
    ///     let sub = m.prefixed_entries(seq![1, 2]);
    ///
    ///     assert(sub.contains_key(seq![]));          // original key [1,2]
    ///     assert(sub[seq![]] == 10);
    ///
    ///     assert(sub.contains_key(seq![3]));         // original key [1,2,3]
    ///     assert(sub[seq![3]] == 20);
    ///
    ///     assert(!sub.contains_key(seq![2]));        // original key [2] was not prefixed
    /// }
    /// ```
    pub open spec fn prefixed_entries(self, prefix: Seq<K>) -> Self {
        Map::new(|k: Seq<K>| self.contains_key(prefix + k), |k: Seq<K>| self[prefix + k])
    }

    /// For every key `k` kept by `prefixed_entries(prefix)`,
    /// the associated value is the one stored at `prefix + k` in the original map.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![seq![1, 2] => 10, seq![1, 2, 3] => 20];
    ///     let p = seq![1, 2];
    ///
    ///     // key inside the sub-map
    ///     assert(m.prefixed_entries(p)[seq![]] == m[p + seq![]]);      // 10
    ///     assert(m.prefixed_entries(p)[seq![3]] == m[p + seq![3]]);    // 20
    /// }
    /// ```
    pub broadcast proof fn lemma_prefixed_entries_get(self, prefix: Seq<K>, k: Seq<K>)
        requires
            self.prefixed_entries(prefix).contains_key(k),
        ensures
            self.prefixed_entries(prefix)[k] == #[trigger] self[prefix + k],
    {
        broadcast use group_map_properties;

    }

    /// A key `k` is in `prefixed_entries(prefix)` exactly when the original map
    /// contains the key `prefix + k`.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![seq![1, 2] => 10, seq![1, 2, 3] => 20];
    ///     let p = seq![1, 2];
    ///
    ///     assert(m.prefixed_entries(p).contains_key(seq![])
    ///            <==> m.contains_key(p + seq![]));
    ///
    ///     assert(m.prefixed_entries(p).contains_key(seq![3])
    ///            <==> m.contains_key(p + seq![3]));
    ///
    ///     assert(!m.prefixed_entries(p).contains_key(seq![2]));
    /// }
    /// ```
    pub broadcast proof fn lemma_prefixed_entries_contains(self, prefix: Seq<K>, k: Seq<K>)
        ensures
            #[trigger] self.prefixed_entries(prefix).contains_key(k) <==> self.contains_key(
                prefix + k,
            ),
    {
        broadcast use group_map_properties;

        let lhs = self.prefixed_entries(prefix);
        let rhs = self;
    }

    /// Inserting `(prefix + k, v)` before taking `prefixed_entries(prefix)`
    /// has the same effect as inserting `(k, v)` into the prefixed map.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let m = map![seq![1, 2] => 10];
    ///     let p = seq![1, 2];
    ///
    ///     let left  = m.insert(p + seq![3], 20).prefixed_entries(p);
    ///     let right = m.prefixed_entries(p).insert(seq![3], 20);
    ///
    ///     assert(left == right);
    /// }
    /// ```
    pub broadcast proof fn lemma_prefixed_entries_insert(self, prefix: Seq<K>, k: Seq<K>, v: V)
        ensures
            #[trigger] self.insert(prefix + k, v).prefixed_entries(prefix) == self.prefixed_entries(
                prefix,
            ).insert(k, v),
    {
        broadcast use group_map_properties;
        broadcast use super::seq::group_seq_axioms;

        #[allow(deprecated)]
        super::seq_lib::lemma_seq_properties::<K>();  // new broadcast group not working here
        broadcast use Map::lemma_prefixed_entries_contains, Map::lemma_prefixed_entries_get;

        let lhs = self.insert(prefix + k, v).prefixed_entries(prefix);
        let rhs = self.prefixed_entries(prefix).insert(k, v);
        assert(lhs =~= rhs) by {
            assert(forall|key| key != k ==> prefix.is_prefix_of(#[trigger] (prefix + key)));
        }
    }

    /// Taking the entries that share `prefix` commutes with `union_prefer_right`:
    /// union the two maps first and then strip the prefix, or strip the prefix from
    /// each map and then union them—the resulting maps are identical.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let a = map![seq![1, 2] => 10, seq![2, 3] => 20];
    ///     let b = map![seq![1, 2] => 99, seq![2, 4] => 40];
    ///     let p = seq![2];
    ///
    ///     assert(
    ///         a.union_prefer_right(b).prefixed_entries(p)
    ///         == a.prefixed_entries(p).union_prefer_right(b.prefixed_entries(p))
    ///     );
    /// }
    /// ```
    pub broadcast proof fn lemma_prefixed_entries_union(self, m: Self, prefix: Seq<K>)
        ensures
            #[trigger] self.union_prefer_right(m).prefixed_entries(prefix) == self.prefixed_entries(
                prefix,
            ).union_prefer_right(m.prefixed_entries(prefix)),
    {
        broadcast use group_map_properties;
        broadcast use
            Map::lemma_prefixed_entries_contains,
            Map::lemma_prefixed_entries_get,
            Map::lemma_prefixed_entries_insert,
        ;

        let lhs = self.union_prefer_right(m).prefixed_entries(prefix);
        let rhs = self.prefixed_entries(prefix).union_prefer_right(m.prefixed_entries(prefix));
        assert(lhs == rhs);
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
pub broadcast proof fn lemma_union_insert_left<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K, v: V)
    requires
        !m2.contains_key(k),
    ensures
        #[trigger] m1.insert(k, v).union_prefer_right(m2) == m1.union_prefer_right(m2).insert(k, v),
{
    assert(m1.insert(k, v).union_prefer_right(m2) =~= m1.union_prefer_right(m2).insert(k, v));
}

pub broadcast proof fn lemma_union_insert_right<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K, v: V)
    ensures
        #[trigger] m1.union_prefer_right(m2.insert(k, v)) == m1.union_prefer_right(m2).insert(k, v),
{
    assert(m1.union_prefer_right(m2.insert(k, v)) =~= m1.union_prefer_right(m2).insert(k, v));
}

pub broadcast proof fn lemma_union_remove_left<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K)
    requires
        m1.contains_key(k),
        !m2.contains_key(k),
    ensures
        #[trigger] m1.union_prefer_right(m2).remove(k) == m1.remove(k).union_prefer_right(m2),
{
    assert(m1.remove(k).union_prefer_right(m2) =~= m1.union_prefer_right(m2).remove(k));
}

pub broadcast proof fn lemma_union_remove_right<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K)
    requires
        !m1.contains_key(k),
        m2.contains_key(k),
    ensures
        #[trigger] m1.union_prefer_right(m2).remove(k) == m1.union_prefer_right(m2.remove(k)),
{
    assert(m1.union_prefer_right(m2.remove(k)) =~= m1.union_prefer_right(m2).remove(k));
}

pub broadcast proof fn lemma_union_dom<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] m1.union_prefer_right(m2).dom() == m1.dom().union(m2.dom()),
{
    assert(m1.dom().union(m2.dom()) =~= m1.union_prefer_right(m2).dom());
}

/// The size of the union of two disjoint maps is equal to the sum of the sizes of the individual maps
pub broadcast proof fn lemma_disjoint_union_size<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.dom().disjoint(m2.dom()),
        m1.dom().finite(),
        m2.dom().finite(),
    ensures
        #[trigger] m1.union_prefer_right(m2).dom().len() == m1.dom().len() + m2.dom().len(),
{
    let u = m1.union_prefer_right(m2);
    assert(u.dom() =~= m1.dom() + m2.dom());  //proves u.dom() is finite
    assert(u.remove_keys(m1.dom()).dom() =~= m2.dom());
    assert(u.remove_keys(m1.dom()).dom().len() == u.dom().len() - m1.dom().len()) by {
        u.lemma_remove_keys_len(m1.dom());
    }
}

pub broadcast group group_map_union {
    lemma_union_dom,
    lemma_union_remove_left,
    lemma_union_remove_right,
    lemma_union_insert_left,
    lemma_union_insert_right,
    lemma_disjoint_union_size,
}

/// submap_of (<=) is transitive.
pub broadcast proof fn lemma_submap_of_trans<K, V>(m1: Map<K, V>, m2: Map<K, V>, m3: Map<K, V>)
    requires
        #[trigger] m1.submap_of(m2),
        #[trigger] m2.submap_of(m3),
    ensures
        m1.submap_of(m3),
{
    assert forall|k| m1.dom().contains(k) implies #[trigger] m3.dom().contains(k) && m1[k]
        == m3[k] by {
        assert(m2.dom().contains(k));
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The domain of a map constructed with `Map::new(fk, fv)` is equivalent to the set constructed with `Set::new(fk)`.
pub broadcast proof fn lemma_map_new_domain<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #[trigger] Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),
{
    assert(Set::new(fk) =~= Set::<K>::new(|k: K| fk(k)));
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The set of values of a map constructed with `Map::new(fk, fv)` is equivalent to
/// the set constructed with `Set::new(|v: V| (exists |k: K| fk(k) && fv(k) == v)`. In other words,
/// the set of all values fv(k) where fk(k) is true.
pub broadcast proof fn lemma_map_new_values<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #[trigger] Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
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
#[deprecated = "Use `broadcast use group_map_properties` instead"]
pub proof fn lemma_map_properties<K, V>()
    ensures
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).dom() == Set::<K>::new(|k: K| fk(k)),  //from lemma_map_new_domain
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            Map::<K, V>::new(fk, fv).values() == Set::<V>::new(
                |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
            ),  //from lemma_map_new_values
{
    broadcast use group_map_properties;

}

pub broadcast group group_map_properties {
    lemma_map_new_domain,
    lemma_map_new_values,
}

pub broadcast group group_map_extra {
    Map::lemma_map_remove_keys_insert,
    Map::lemma_filter_keys_insert,
    Map::lemma_prefixed_entries_get,
    Map::lemma_prefixed_entries_contains,
    Map::lemma_prefixed_entries_insert,
    Map::lemma_prefixed_entries_union,
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
