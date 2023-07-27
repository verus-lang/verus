#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
use crate::set::*;
use core::marker;
use crate::set_lib::lemma_set_properties;


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
/// In general, a map might be infinite.
/// To work specifically with finite maps, see the [`self.finite()`](Set::finite) predicate.
///
/// Maps can be constructed in a few different ways:
///  * [`Map::empty()`] constructs an empty map.
///  * [`Map::new`] and [`Map::total`] construct a map given functions that specify its domain and the mapping
///     from keys to values (a _map comprehension_).
///  * The [`map!`] macro, to construct small maps of a fixed size.
///  * By manipulating an existing map with [`Map::insert`] or [`Map::remove`].
///
/// To prove that two maps are equal, it is usually easiest to use the [`assert_maps_equal!`] macro.

#[verifier(external_body)]
#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct Map<K, V> {
    dummy: marker::PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    /// An empty map.

    pub spec fn empty() -> Map<K, V>;

    /// Gives a `Map<K, V>` whose domain contains every key, and maps each key
    /// to the value given by `fv`.

    pub open spec fn total(fv: impl Fn(K) -> V) -> Map<K, V> {
        Set::full().mk_map(fv)
    }

    /// Gives a `Map<K, V>` whose domain is given by the boolean predicate on keys `fk`,
    /// and maps each key to the value given by `fv`.

    pub open spec fn new(fk: impl Fn(K) -> bool, fv: impl Fn(K) -> V) -> Map<K, V> {
        Set::new(fk).mk_map(fv)
    }

    /// The domain of the map as a set.

    pub spec fn dom(self) -> Set<K>;

    /// The set of keys mapped to by the domain of the map
 
    pub open spec fn values(self) -> Set<V> {
        Set::<V>::new(|v: V| self.contains_value(v))
    }

    /// Gets the value that the given key `key` maps to.
    /// For keys not in the domain, the result is meaningless and arbitrary.

    pub spec fn index(self, key: K) -> V
        recommends self.dom().contains(key);

    /// `[]` operator, synonymous with `index`

    #[verifier(inline)]
    pub open spec fn spec_index(self, key: K) -> V
        recommends self.dom().contains(key)
    {
        self.index(key)
    }

    /// Inserts the given (key, value) pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.

    pub spec fn insert(self, key: K, value: V) -> Map<K, V>;

    /// Removes the given key and its associated value from the map.
    ///
    /// If the key is already absent from the map, then the map is left unchanged.

    pub spec fn remove(self, key: K) -> Map<K, V>;

    // Returns the number of key-value pairs in the map

    pub open spec fn len(self) -> nat {
        self.dom().len()
    }

    /// DEPRECATED: use =~= or =~~= instead.
    /// Returns true if the two maps are pointwise equal, i.e.,
    /// they have the same domains and the corresponding values are equal
    /// for each key. This is equivalent to the maps being actually equal
    /// by [`axiom_map_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it may be easier
    /// to use the general-purpose `=~=` or `=~~=` or
    /// to use the [`assert_maps_equal!`] macro, rather than using `.ext_equal` directly.

    #[deprecated = "use =~= or =~~= instead"]
    pub open spec fn ext_equal(self, m2: Map<K, V>) -> bool {
        self =~= m2
    }

    /// Returns true if the key `k` is in the domain of `self`.

    #[verifier(inline)]
    pub open spec fn contains_key(self, k: K) -> bool {
        self.dom().contains(k)
    }

    /// Returns true if the value `v` is in the map of `self`.

    pub open spec fn contains_value(self, v: V) -> bool {
        exists|i: K| #[trigger] self.dom().contains(i) && self[i] == v
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

    pub open spec fn le(self, m2: Self) -> bool {
        forall|k: K| #[trigger] self.dom().contains(k) ==>
            #[trigger] m2.dom().contains(k) && self[k] == m2[k]
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
    /// assert_maps_equal!(
    ///    map![1 => 10, 2 => 11].union_prefer_right(map![1 => 20, 3 => 13]),
    ///    map![1 => 20, 2 => 11, 3 => 13],
    /// );
    /// ```

    pub open spec fn union_prefer_right(self, m2: Self) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) || m2.dom().contains(k),
            |k: K| if m2.dom().contains(k) { m2[k] } else { self[k] }
        )
    }

    /// Removes the given keys and their associated values from the map.
    ///
    /// Ignores any key in `keys` which is not in the domain of `self`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert_maps_equal!(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4}),
    ///    map![1 => 10],
    /// );
    /// ```

    pub open spec fn remove_keys(self, keys: Set<K>) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) && !keys.contains(k),
            |k: K| self[k]
        )
    }

    /// Complement to `remove_keys`. Restricts the map to (key, value) pairs
    /// for keys that are _in_ the given set; that is, it removes any keys
    /// _not_ in the set.
    ///
    /// ## Example
    ///
    /// ```rust
    /// assert_maps_equal!(
    ///    map![1 => 10, 2 => 11, 3 => 12].remove_keys(set!{2, 3, 4}),
    ///    map![2 => 11, 3 => 12],
    /// );
    /// ```

    pub open spec fn restrict(self, keys: Set<K>) -> Self {
        Self::new(
            |k: K| self.dom().contains(k) && keys.contains(k),
            |k: K| self[k]
        )
    }

    /// Returns `true` if and only if the given key maps to the same value or does not exist in self and m2.
    
    pub open spec fn equal_on_key(self, m2: Self, key: K) -> bool
    {
        ||| (!self.dom().contains(key) && !m2.dom().contains(key))
        ||| (self.dom().contains(key) && m2.dom().contains(key) && self[key] == m2[key])
    }

    /// Returns `true` if the two given maps agree on all keys that their domains
    /// share in common.

    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==>
            self[k] == m2[k]
    }

    #[verifier(external_body)]
    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == Map::<K, V>::empty(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == Map::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    /// todo fill in documentation

    #[verifier(external_body)]
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == Map::remove(*old(self), key),
            v == old(self)[key],
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_map_keys<J>(
        tracked old_map: Map<K, V>,
        key_map: Map<J, K>
    ) -> (tracked new_map: Map<J, V>)
        requires
            forall |j| #![auto] key_map.dom().contains(j) ==> old_map.dom().contains(key_map.index(j)),
            forall |j1, j2| #![auto]
                !equal(j1, j2) && key_map.dom().contains(j1) && key_map.dom().contains(j2)
                ==> !equal(key_map.index(j1), key_map.index(j2))
        ensures
            forall |j| #[trigger] new_map.dom().contains(j) <==> key_map.dom().contains(j),
            forall |j| key_map.dom().contains(j) ==>
                new_map.dom().contains(j) &&
                #[trigger] new_map.index(j) == old_map.index(key_map.index(j)),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_remove_keys(tracked &mut self, keys: Set<K>)
        -> (tracked out_map: Map<K, V>)
        requires
            keys.subset_of(old(self).dom())
        ensures
            self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    {
        unimplemented!();
    }

    /// Map a function `f` over all (k, v) pairs in `self`.
    pub open spec fn map_entries<W>(self, f: FnSpec(K, V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(k, self[k]))
    }

    /// Map a function `f` over the values in `self`.
    pub open spec fn map_values<W>(self, f: FnSpec(V) -> W) -> Map<K, W> {
        Map::new(|k: K| self.contains_key(k), |k: K| f(self[k]))
    }

    /// Returns `true` if and only if a map is injective
    pub open spec fn is_injective(self) -> bool {
        forall |x: K, y: K| x != y && self.dom().contains(x) && self.dom().contains(y) ==> #[trigger] self[x] != #[trigger] self[y]
    }

    /// Swaps map keys and values. Values are not required to be unique; no
    /// promises on which key is chosen on the intersection.
    pub open spec fn invert(self) -> Map<V,K> 
    {
        Map::<V,K>::new(
            |v: V| self.contains_value(v),
            |v: V| choose |k: K| self.contains_pair(k,v)
        )
    }
}

impl Map<int,int> {

    /// Returns `true` if a map is monotonic -- that is, if the mapping between ordered sets 
    /// preserves the regular `<=` ordering on integers.
    pub open spec fn is_monotonic(self) -> bool {
        forall |x: int, y: int| self.dom().contains(x) && self.dom().contains(y) && x <= y 
            ==> #[trigger] self[x] <= #[trigger] self[y]
    }

    /// Returns `true` if and only if a map is monotonic, only considering keys greater than
    /// or equal to start
    pub open spec fn monotonic_from(self, start: int) -> bool {
        forall |x: int, y: int| self.dom().contains(x) && self.dom().contains(y) && start <= x <= y 
            ==> #[trigger] self[x] <= #[trigger] self[y]
    }

}

// Proven lemmas

/// Removing a key from a map that previously contained that key results
/// in a length that is one less than the original length.
pub proof fn lemma_remove_key_len<K,V>(m: Map<K,V>, key: K)
    requires
        m.dom().contains(key),
        m.dom().finite(),
    ensures
        m.dom().len() == 1 + m.remove(key).dom().len(),
{}

/// The domain of a map after removing a key is equivalent to removing the key from 
/// the domain of the original map.
pub proof fn lemma_remove_equivalency<K,V>(m: Map<K,V>, key: K)
    ensures
        m.remove(key).dom() == m.dom().remove(key),
{}

/// Removing a set of n keys from a map that previously contained all n keys
/// results in a domain of size n less than the original domain.
pub proof fn lemma_remove_keys_len<K,V>(m: Map<K,V>, keys: Set<K>)
    requires
        forall |k: K| #[trigger] keys.contains(k) ==> m.contains_key(k),
        keys.finite(),
        m.dom().finite(),
    ensures 
        m.remove_keys(keys).dom().len() == m.dom().len() - keys.len(),
    decreases
        keys.len(),
{
    lemma_set_properties::<K>();
    if keys.len() > 0 {
        let key = keys.choose();
        let val = m[key];
        lemma_remove_keys_len(m.remove(key),keys.remove(key));
        assert(m.remove(key).remove_keys(keys.remove(key)) =~= m.remove_keys(keys));
    }
    else {
        assert(m.remove_keys(keys) =~= m);
    }
}

/// The size of the union of two maps is equal to the sum of the sizes of the individual maps
pub proof fn lemma_disjoint_union_size<K,V>(m1: Map<K,V>, m2: Map<K,V>)
    requires
        m1.dom().disjoint(m2.dom()),
        m1.dom().finite(),
        m2.dom().finite(),
    ensures
        m1.union_prefer_right(m2).dom().len() == m1.dom().len() + m2.dom().len(),
{
    let u = m1.union_prefer_right(m2);
    assert(u.dom() =~= m1.dom() + m2.dom()); //proves u.dom() is finite
    assert(u.remove_keys(m1.dom()).dom() =~= m2.dom());
    assert(u.remove_keys(m1.dom()).dom().len() == u.dom().len() - m1.dom().len()) by {
        lemma_remove_keys_len(u, m1.dom());
    }
}

/// The function `invert` results in an injective map
pub proof fn lemma_invert_is_injective<K,V>(m: Map<K,V>)
    ensures
        m.invert().is_injective(),
{
    assert forall |x: V, y: V| x != y && m.invert().dom().contains(x) && m.invert().dom().contains(y) 
                implies #[trigger] m.invert()[x] != #[trigger] m.invert()[y] by {
        let i = choose |i: K| #[trigger] m.dom().contains(i) && m[i] == x;
        assert(m.contains_pair(i,x));
        let j = choose |j: K| m.contains_pair(j,x) && m.invert()[x] == j;

        let k = choose |k: K| #[trigger] m.dom().contains(k) && m[k] == y;
        assert(m.contains_pair(k,y));
        let l = choose |l: K| m.contains_pair(l,y) && m.invert()[y] == l && l != j;
    }   
}

// Trusted axioms

/* REVIEW: this is simpler than the two separate axioms below -- would this be ok?
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key])),
{
}
*/

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key])),
{
}

// REVIEW: this is currently a special case that is hard-wired into the verifier
// It implements a version of https://github.com/FStarLang/FStar/pull/2954 .
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
{
}

/// The domain of the empty map is the empty set
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        m.remove(key2)[key1] == m[key1],
{
}

// Ported from Dafny prelude
/// The domain of a map constructed with `Map::new(fk, fv)` is equivalent to the set constructed with `Set::new(fk)`.
pub proof fn lemma_map_new_domain<K,V>(fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V)
    ensures
        #[trigger] Map::<K,V>::new(fk,fv).dom() == Set::<K>::new(|k: K| fk(k))
{
    assert(Set::new(fk) =~= Set::<K>::new(|k: K| fk(k)));
}

// Ported from Dafny prelude
/// The set of values of a map constructed with `Map::new(fk, fv)` is equivalent to 
/// the set constructed with `Set::new(|v: V| (exists |k: K| fk(k) && fv(k) == v)`. In other words,
/// the set of all values fv(k) where fk(k) is true.
pub proof fn lemma_map_new_values<K,V>(fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V)
    ensures
        #[trigger] Map::<K,V>::new(fk,fv).values() == Set::<V>::new(|v: V| (exists |k: K| #[trigger] fk(k) && #[trigger] fv(k) == v)),
{
    let keys = Set::<K>::new(fk);
    let values = Map::<K,V>::new(fk,fv).values();
    let map = Map::<K,V>::new(fk,fv);

    assert(map.dom() =~= keys);
    assert(forall |k: K| #[trigger] fk(k) ==> keys.contains(k));
    assert(values =~= Set::<V>::new(|v: V| (exists |k: K| #[trigger] fk(k) && #[trigger] fv(k) == v)));
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
}

// magic auto style bundle of lemmas that Dafny considers when proving properties of maps
pub proof fn lemma_map_properties<K,V>()
    ensures
    forall |fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V| #[trigger] Map::<K,V>::new(fk,fv).dom()
            == Set::<K>::new(|k: K| fk(k)), //lemma_map_new_domain
    forall |fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V| #[trigger] Map::<K,V>::new(fk,fv).values() 
            == Set::<V>::new(|v: V| exists |k: K| #[trigger] fk(k) && #[trigger] fv(k) == v),  //lemma_map_new_values
{
    assert forall |fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V| 
        #[trigger] Map::<K,V>::new(fk,fv).dom() == Set::<K>::new(|k: K| fk(k)) by {
            lemma_map_new_domain(fk, fv);
        }
    assert forall |fk: FnSpec(K) -> bool, fv: FnSpec(K) -> V| #[trigger] Map::<K,V>::new(fk,fv).values() 
        == Set::<V>::new(|v: V| exists |k: K| #[trigger] fk(k) && #[trigger] fv(k) == v) by {
            lemma_map_new_values(fk, fv);
        }
}

// Macros

#[doc(hidden)]
#[macro_export]
macro_rules! map_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::map::Map::empty()
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::map::map_internal!($($tail)*))
    };
}

#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_map<K, V>(m: Map<K, V>) -> Map<K, V> { m }

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
        ::builtin_macros::verus_proof_macro_exprs!($crate::map::assert_maps_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_maps_equal_internal {
    (::builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_maps_equal_internal!($m1, $m2)
    };
    (::builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_maps_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_maps_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $crate::map::check_argument_is_map($m1);
        #[verifier::spec] let m2 = $crate::map::check_argument_is_map($m2);
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                ::builtin::ensures([
                    ::builtin::imply(#[verifier::trigger] m1.dom().contains($k), m2.dom().contains($k))
                    && ::builtin::imply(m2.dom().contains($k), m1.dom().contains($k))
                    && ::builtin::imply(m1.dom().contains($k) && m2.dom().contains($k),
                        ::builtin::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(m1, m2));
        });
    }
}

#[doc(hidden)]
pub use assert_maps_equal_internal;
pub use assert_maps_equal;

impl<K, V> Map<K, V> {
    pub proof fn tracked_map_keys_in_place(
        #[verifier::proof] &mut self,
        key_map: Map<K, K>
    )
    requires
        forall|j| #![auto] key_map.dom().contains(j) ==> old(self).dom().contains(key_map.index(j)),
        forall|j1, j2| #![auto]
            j1 != j2 && key_map.dom().contains(j1) && key_map.dom().contains(j2) ==>
            key_map.index(j1) != key_map.index(j2),
    ensures
        forall|j| #[trigger] self.dom().contains(j) == key_map.dom().contains(j),
        forall|j| key_map.dom().contains(j) ==>
            self.dom().contains(j) &&
            #[trigger] self.index(j) == old(self).index(key_map.index(j)),
    {
        #[verifier::proof] let mut tmp = Self::tracked_empty();
        crate::modes::tracked_swap(&mut tmp, self);
        #[verifier::proof] let mut tmp = Self::tracked_map_keys(tmp, key_map);
        crate::modes::tracked_swap(&mut tmp, self);
    }
}

} // verus!
