use super::map::GenericMap;
#[macro_use]
use super::map::{Map, IMap, assert_maps_equal, assert_maps_equal_internal};
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use super::gset::*;
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::set_lib::*;

verus! {

broadcast use {
    super::map::group_map_axioms,
    super::map::group_map_internal_axioms,
    super::set::group_set_lemmas,
};

impl<K, V, FINITE: Finiteness> GenericMap<K, V, FINITE> {
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
    pub open spec fn values(self) -> GSet<V, FINITE> {
        self.dom().map(|k: K| self.index(k))
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
    pub open spec fn kv_pairs(self) -> GSet<(K, V), FINITE> {
        self.dom().map(|k: K| (k, self[k]))
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

    /// Returns `true` if and only if the given key maps to the same value or does not exist in self and m2.
    pub open spec fn is_equal_on_key(self, m2: Self, key: K) -> bool {
        ||| (!self.dom().contains(key) && !m2.dom().contains(key))
        ||| (self.dom().contains(key) && m2.dom().contains(key) && self[key] == m2[key])
    }

    /// Returns `true` if the two given maps agree on all keys that their domains share
    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==> self[k] == m2[k]
    }

    /// Returns `true` if and only if a map is injective
    pub open spec fn is_injective(self) -> bool {
        forall|x: K, y: K|
            x != y && self.dom().contains(x) && self.dom().contains(y) ==> #[trigger] self[x]
                != #[trigger] self[y]
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
        broadcast use group_set_properties;
        lemma_gset_remove_len(self.dom(), key);
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
    pub proof fn lemma_remove_keys_len(self, keys: GSet<K, FINITE>)
        requires
            keys <= self.dom(),
            keys.finite(),  // not clear why this is necessary
            self.dom().finite(),
        ensures
            self.remove_keys(keys).dom().len() == self.dom().len() - keys.len(),
        decreases keys.len(),
    {
        broadcast use group_set_properties;

        if keys.len() > 0 {
            let key = keys.choose();
            lemma_gset_choose_len(keys);
            lemma_gset_remove_len(keys, key);
            assert(keys.remove(key).len() < keys.len());
            self.remove(key).lemma_remove_keys_len(keys.remove(key));  // recurse

            // trigger extensionality
            assert(self.remove_keys(keys).dom() == self.remove(key).remove_keys(
                keys.remove(key),
            ).dom());
        } else {
            // keys is empty, so remove_keys is a noop
            self.remove_keys(keys).dom().to_infinite().congruent_len(self.remove_keys(keys).dom());
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
    pub broadcast proof fn lemma_map_remove_keys_insert(self, r: GSet<K, FINITE>, k: K, v: V)
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

impl<K, V> IMap<Seq<K>, V> {
    proof fn lemma_seq_add_left_cancel(prefix: Seq<K>, s1: Seq<K>, s2: Seq<K>)
        ensures
            #[trigger] (prefix + s1 == prefix + s2) ==> s1 == s2,
    {
        broadcast use super::seq::group_seq_axioms;
        if prefix + s1 == prefix + s2 {
            assert((prefix + s1).len() == (prefix + s2).len());
            assert(s1.len() == s2.len());
            assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
                assert(0 <= prefix.len() + i < (prefix + s1).len());
                assert((prefix + s1)[prefix.len() + i] == s1[i]);
                assert((prefix + s2)[prefix.len() + i] == s2[i]);
                assert((prefix + s1)[prefix.len() + i] == (prefix + s2)[prefix.len() + i]);
            }
            assert(s1 =~= s2);
            assert(s1 == s2);
        }
    }

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
        IMap::new(|k: Seq<K>| self.contains_key(prefix + k), |k: Seq<K>| self[prefix + k])
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
        let fk = |kk: Seq<K>| self.contains_key(prefix + kk);
        let fv = |kk: Seq<K>| self[prefix + kk];
        super::gmap::lemma_infinite_new_ensures(fk, fv);
        assert(self.prefixed_entries(prefix)[k] == fv(k));
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

        let fk = |kk: Seq<K>| self.contains_key(prefix + kk);
        lemma_imap_new_domain(fk, |kk: Seq<K>| self[prefix + kk]);
        super::iset::lemma_iset_new(fk, k);
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
        broadcast use {
            lemma_prefixed_entries_contains_generic,
            lemma_prefixed_entries_get_generic,
        };

        let lhs = self.insert(prefix + k, v).prefixed_entries(prefix);
        let rhs = self.prefixed_entries(prefix).insert(k, v);
        super::gmap::lemma_map_insert_domain(self.prefixed_entries(prefix).to_gmap(), k, v);
        super::gmap::lemma_map_insert_domain(self.to_gmap(), prefix + k, v);
        assert forall|key: Seq<K>| lhs.contains_key(key) <==> rhs.contains_key(key) by {
            self.insert(prefix + k, v).lemma_prefixed_entries_contains(prefix, key);
            self.lemma_prefixed_entries_contains(prefix, key);
            if lhs.contains_key(key) {
                assert(self.insert(prefix + k, v).contains_key(prefix + key));
                if prefix + key == prefix + k {
                    Self::lemma_seq_add_left_cancel(prefix, key, k);
                    assert(key == k);
                } else {
                    super::gset::lemma_gset_insert_different(self.dom().to_gset(), prefix + key, prefix + k);
                    assert(self.dom().to_gset().insert(prefix + k).contains(prefix + key));
                    assert(self.contains_key(prefix + key));
                }
                assert(rhs.contains_key(key));
            } else {
                assert(!self.insert(prefix + k, v).contains_key(prefix + key));
                assert(!rhs.contains_key(key));
            }
        }
        assert forall|key: Seq<K>| lhs.contains_key(key) implies lhs[key] == rhs[key] by {
            assert(lhs.contains_key(key));
            if key == k {
                self.insert(prefix + k, v).lemma_prefixed_entries_contains(prefix, key);
                self.insert(prefix + k, v).lemma_prefixed_entries_get(prefix, key);
                super::gmap::lemma_map_insert_same(self.to_gmap(), prefix + k, v);
                super::gmap::lemma_map_insert_same(self.prefixed_entries(prefix).to_gmap(), k, v);
            } else {
                assert(prefix + key != prefix + k) by {
                    if prefix + key == prefix + k {
                        Self::lemma_seq_add_left_cancel(prefix, key, k);
                        assert(key == k);
                        assert(false);
                    }
                }
                self.insert(prefix + k, v).lemma_prefixed_entries_get(prefix, key);
                self.lemma_prefixed_entries_get(prefix, key);
                super::gmap::lemma_map_insert_different(self.to_gmap(), prefix + key, prefix + k, v);
                super::gmap::lemma_map_insert_different(self.prefixed_entries(prefix).to_gmap(), key, k, v);
            }
        }
        super::map::lemma_imap_ext_equal(lhs, rhs);
        assert(lhs.to_gmap().congruent(rhs.to_gmap())) by {
            assert forall|key: Seq<K>| lhs.to_gmap().contains_key(key) <==> rhs.to_gmap().contains_key(key) by {
                super::map::lemma_imap_dom_contains_bridge(lhs, key);
                super::map::lemma_imap_dom_contains_bridge(rhs, key);
                assert(lhs.to_gmap().contains_key(key) == lhs.contains_key(key));
                assert(rhs.to_gmap().contains_key(key) == rhs.contains_key(key));
            }
            assert forall|key: Seq<K>| lhs.to_gmap().contains_key(key) implies lhs.to_gmap()[key] == rhs.to_gmap()[key] by {
                if lhs.to_gmap().contains_key(key) {
                    super::map::lemma_imap_dom_contains_bridge(lhs, key);
                    super::map::lemma_imap_dom_contains_bridge(rhs, key);
                    assert(lhs.contains_key(key));
                    assert(lhs[key] == rhs[key]);
                    assert(lhs[key] == lhs.to_gmap()[key]);
                    assert(rhs[key] == rhs.to_gmap()[key]);
                }
            }
        }
        super::gmap::lemma_congruence_extensionality(lhs.to_gmap(), rhs.to_gmap());
        assert(lhs == rhs);
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
            lemma_prefixed_entries_contains_generic,
            lemma_prefixed_entries_get_generic,
            lemma_prefixed_entries_insert_generic,
        ;

        let lhs = self.union_prefer_right(m).prefixed_entries(prefix);
        let rhs = self.prefixed_entries(prefix).union_prefer_right(m.prefixed_entries(prefix));
        self.0.lemma_union_prefer_right(m.0);
        self.prefixed_entries(prefix).0.lemma_union_prefer_right(m.prefixed_entries(prefix).0);

        assert forall|key: Seq<K>| lhs.contains_key(key) <==> rhs.contains_key(key) by {
            self.union_prefer_right(m).lemma_prefixed_entries_contains(prefix, key);
            self.lemma_prefixed_entries_contains(prefix, key);
            m.lemma_prefixed_entries_contains(prefix, key);
            super::iset::lemma_iset_union(
                self.prefixed_entries(prefix).dom(),
                m.prefixed_entries(prefix).dom(),
                key,
            );
        }
        assert forall|key: Seq<K>| lhs.contains_key(key) implies lhs[key] == rhs[key] by {
            assert(lhs.contains_key(key));
            self.union_prefer_right(m).lemma_prefixed_entries_get(prefix, key);
            if m.prefixed_entries(prefix).contains_key(key) {
                m.lemma_prefixed_entries_get(prefix, key);
            } else {
                self.lemma_prefixed_entries_get(prefix, key);
            }
        }
        super::map::lemma_imap_ext_equal(lhs, rhs);
        assert(lhs.to_gmap().congruent(rhs.to_gmap())) by {
            assert forall|key: Seq<K>| lhs.to_gmap().contains_key(key) <==> rhs.to_gmap().contains_key(key) by {
                super::map::lemma_imap_dom_contains_bridge(lhs, key);
                super::map::lemma_imap_dom_contains_bridge(rhs, key);
                assert(lhs.to_gmap().contains_key(key) == lhs.contains_key(key));
                assert(rhs.to_gmap().contains_key(key) == rhs.contains_key(key));
            }
            assert forall|key: Seq<K>| lhs.to_gmap().contains_key(key) implies lhs.to_gmap()[key] == rhs.to_gmap()[key] by {
                if lhs.to_gmap().contains_key(key) {
                    super::map::lemma_imap_dom_contains_bridge(lhs, key);
                    super::map::lemma_imap_dom_contains_bridge(rhs, key);
                    assert(lhs.contains_key(key));
                    assert(lhs[key] == rhs[key]);
                    assert(lhs[key] == lhs.to_gmap()[key]);
                    assert(rhs[key] == rhs.to_gmap()[key]);
                }
            }
        }
        super::gmap::lemma_congruence_extensionality(lhs.to_gmap(), rhs.to_gmap());
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
    assert(m1.insert(k, v).union_prefer_right(m2) =~= m1.union_prefer_right(m2).insert(k, v));  // issue #1534
}

pub broadcast proof fn lemma_union_insert_right<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K, v: V)
    ensures
        #[trigger] m1.union_prefer_right(m2.insert(k, v)) == m1.union_prefer_right(m2).insert(k, v),
{
    assert(m1.union_prefer_right(m2.insert(k, v)) =~= m1.union_prefer_right(m2).insert(k, v));  // issue #1534
}

pub broadcast proof fn lemma_union_remove_left<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K)
    requires
        m1.contains_key(k),
        !m2.contains_key(k),
    ensures
        #[trigger] m1.union_prefer_right(m2).remove(k) == m1.remove(k).union_prefer_right(m2),
{
    assert(m1.remove(k).union_prefer_right(m2) =~= m1.union_prefer_right(m2).remove(k));  // issue #1534
}

pub broadcast proof fn lemma_union_remove_right<K, V>(m1: Map<K, V>, m2: Map<K, V>, k: K)
    requires
        !m1.contains_key(k),
        m2.contains_key(k),
    ensures
        #[trigger] m1.union_prefer_right(m2).remove(k) == m1.union_prefer_right(m2.remove(k)),
{
    assert(m1.union_prefer_right(m2.remove(k)) =~= m1.union_prefer_right(m2).remove(k));  // issue #1534
}

pub broadcast proof fn lemma_union_dom<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] m1.union_prefer_right(m2).dom() == (m1.dom() + m2.dom()),
{
    let lhs = m1.union_prefer_right(m2).dom();
    let rhs = (m1.dom() + m2.dom());
    m1.lemma_union_prefer_right(m2);
    assert(lhs =~= rhs) by {
        assert forall|k: K| #[trigger] lhs.contains(k) == rhs.contains(k) by {
            super::set::lemma_set_to_infinite_contains(lhs, k);
            super::set::lemma_set_to_infinite_contains(m1.dom(), k);
            super::set::lemma_set_to_infinite_contains(m2.dom(), k);
            super::iset::lemma_iset_union(m1.dom().to_infinite(), m2.dom().to_infinite(), k);
            lemma_set_union(m1.dom(), m2.dom(), k);
        }
    }
    lemma_set_ext_equal_eq(lhs, rhs);
    assert(lhs == rhs);
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
    lemma_union_dom(m1, m2);
    assert(u.dom() == (m1.dom() + m2.dom()));  //proves u.dom() is finite
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
pub broadcast proof fn lemma_submap_of_trans<K, V, FINITE: Finiteness>(
    m1: GenericMap<K, V, FINITE>,
    m2: GenericMap<K, V, FINITE>,
    m3: GenericMap<K, V, FINITE>,
)
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
/// The domain of a map constructed with `IMap::new(fk, fv)` is equivalent to the set constructed with `ISet::new(fk)`.
pub broadcast proof fn lemma_imap_new_domain<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #[trigger] IMap::<K, V>::new(fk, fv).dom() == ISet::<K>::new(|k: K| fk(k)),
{
    let map = IMap::<K, V>::new(fk, fv);
    let keys = ISet::<K>::new(|k: K| fk(k));
    super::gmap::lemma_infinite_new_ensures(fk, fv);
    assert forall|k: K| map.dom().contains(k) == keys.contains(k) by {
        super::iset::lemma_iset_new(|x| fk(x), k);
    }
    super::iset::lemma_iset_ext_equal(map.dom(), keys);
    super::iset::lemma_iset_ext_equal_eq(map.dom(), keys);
}

/// The domain of a map constructed with `Map::new(key_set, fv)` is equivalent to `key_set`.
pub broadcast proof fn lemma_map_new_domain<K, V>(key_set: Set<K>, fv: spec_fn(K) -> V)
    ensures
        #[trigger] Map::<K, V>::new(key_set, fv).dom() == key_set,
{
    assert(Map::<K, V>::new(key_set, fv).dom() =~= key_set);  // issue #1534
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The set of values of a map constructed with `Map::new(fk, fv)` is equivalent to
/// the set constructed with `ISet::new(|v: V| (exists |k: K| fk(k) && fv(k) == v)`. In other words,
/// the set of all values fv(k) where fk(k) is true.
pub broadcast proof fn lemma_imap_new_values<K, V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        #[trigger] IMap::<K, V>::new(fk, fv).values() == ISet::<V>::new(
            |v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),
        ),
{
    let keys = ISet::<K>::new(fk);
    let values = IMap::<K, V>::new(fk, fv).values();
    let map = IMap::<K, V>::new(fk, fv);
    let target = ISet::<V>::new(|v: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v));
    lemma_imap_new_domain(fk, fv);
    super::iset::lemma_iset_map_contains(map.dom(), |k: K| map[k]);
    assert forall|v: V| values.contains(v) == target.contains(v) by {
        super::iset::lemma_iset_new(|vv: V| (exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == vv), v);
        if values.contains(v) {
            let k = choose|k: K| map.dom().contains(k) && map[k] == v;
            assert(map.dom().contains(k));
            assert(map[k] == v);
            assert(keys.contains(k));
            super::iset::lemma_iset_new(fk, k);
            assert(fk(k));
            assert(fv(k) == map[k]);
        }
        if target.contains(v) {
            let k = choose|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v;
            super::iset::lemma_iset_new(fk, k);
            assert(keys.contains(k));
            assert(map.dom().contains(k));
            assert(map[k] == fv(k));
            assert(map[k] == v);
            assert(values.contains(v));
        }
    }
    super::iset::lemma_iset_ext_equal(values, target);
    assert(values =~= target);
    super::iset::lemma_iset_ext_equal_eq(values, target);
}

/// Properties of maps from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
#[deprecated = "Use `broadcast use group_map_properties` instead"]
pub proof fn lemma_map_properties<K, V>()
    ensures
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            IMap::<K, V>::new(fk, fv).dom() == ISet::<K>::new(|k: K| fk(k)),  //from lemma_imap_new_domain
        forall|fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V| #[trigger]
            IMap::<K, V>::new(fk, fv).values() == ISet::<V>::new(
                |v: V| exists|k: K| #[trigger] fk(k) && #[trigger] fv(k) == v,
            ),  //from lemma_imap_new_values
{
    broadcast use group_map_properties;

}

pub broadcast group group_map_properties {
    lemma_imap_new_domain,
    lemma_imap_new_values,
}

pub broadcast proof fn lemma_map_remove_keys_insert_generic<K, V, FINITE: Finiteness>(
    m: GenericMap<K, V, FINITE>,
    r: GSet<K, FINITE>,
    k: K,
    v: V,
)
    ensures
        #[trigger] m.insert(k, v).remove_keys(r) == if r.contains(k) {
            m.remove_keys(r)
        } else {
            m.remove_keys(r).insert(k, v)
        },
{
    m.lemma_map_remove_keys_insert(r, k, v);
}

pub broadcast proof fn lemma_filter_keys_insert_generic<K, V, FINITE: Finiteness>(
    m: GenericMap<K, V, FINITE>,
    p: spec_fn(K) -> bool,
    k: K,
    v: V,
)
    ensures
        #[trigger] m.insert(k, v).filter_keys(p) == (if p(k) {
            m.filter_keys(p).insert(k, v)
        } else {
            m.filter_keys(p)
        }),
{
    m.lemma_filter_keys_insert(p, k, v);
}

pub broadcast proof fn lemma_prefixed_entries_get_generic<K, V>(
    m: IMap<Seq<K>, V>,
    prefix: Seq<K>,
    k: Seq<K>,
)
    requires
        m.prefixed_entries(prefix).contains_key(k),
    ensures
        m.prefixed_entries(prefix)[k] == #[trigger] m[prefix + k],
{
    m.lemma_prefixed_entries_get(prefix, k);
}

pub broadcast proof fn lemma_prefixed_entries_contains_generic<K, V>(
    m: IMap<Seq<K>, V>,
    prefix: Seq<K>,
    k: Seq<K>,
)
    ensures
        #[trigger] m.prefixed_entries(prefix).contains_key(k) <==> m.contains_key(prefix + k),
{
    m.lemma_prefixed_entries_contains(prefix, k);
}

pub broadcast proof fn lemma_prefixed_entries_insert_generic<K, V>(
    m: IMap<Seq<K>, V>,
    prefix: Seq<K>,
    k: Seq<K>,
    v: V,
)
    ensures
        #[trigger] m.insert(prefix + k, v).prefixed_entries(prefix) == m.prefixed_entries(
            prefix,
        ).insert(k, v),
{
    m.lemma_prefixed_entries_insert(prefix, k, v);
}

pub broadcast proof fn lemma_prefixed_entries_union_generic<K, V>(
    m1: IMap<Seq<K>, V>,
    m2: IMap<Seq<K>, V>,
    prefix: Seq<K>,
)
    ensures
        #[trigger] m1.union_prefer_right(m2).prefixed_entries(prefix) == m1.prefixed_entries(
            prefix,
        ).union_prefer_right(m2.prefixed_entries(prefix)),
{
    m1.lemma_prefixed_entries_union(m2, prefix);
}

pub broadcast group group_map_extra {
    lemma_map_remove_keys_insert_generic,
    lemma_filter_keys_insert_generic,
    lemma_prefixed_entries_get_generic,
    lemma_prefixed_entries_contains_generic,
    lemma_prefixed_entries_insert_generic,
    lemma_prefixed_entries_union_generic,
}

pub proof fn lemma_values_finite<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
    ensures
        m.values().finite(),
{
    // This proof is trivial now, since values() is defined as the map() of a finite source map.
}

} // verus!
