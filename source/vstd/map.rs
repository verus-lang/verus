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
/// In general, a map might be infinite.
/// To work specifically with finite maps, see the [`self.finite()`](Set::finite) predicate.
/// TODO(jonh): update docs here when we have Map/IMap type split.
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
pub tracked struct GMap<K, V, const Finite: bool> {
    mapping: spec_fn(K) -> Option<V>,
}

/// Map<K,V> is a type synonym for map whose membership is finite (known at typechecking time).
pub type Map<K, V> = GMap<K, V, true>;

pub broadcast proof fn lemma_map_finite_from_type<K, V>(m: Map<K, V>)
ensures #[trigger] m.dom().finite()
{
    admit();
}

/// IMap<K,V> is a type synonym a set whose membership may be infinite (but can be
/// proven finite at verification time).
pub type IMap<K, V> = GMap<K, V, false>;

impl<K, V, const Finite: bool> GMap<K, V, Finite> {
    /// An empty map.
    pub closed spec fn empty() -> Self {
        GMap { mapping: |k| None }
    }

    /// The domain of the map as a set.
    pub closed spec fn dom(self) -> GSet<K, Finite> {
        // TODO(jonh) be clevererer
        // I need an expression whose type changes depending on the context.
        // Options
        // - we're back at the multiple-impls-for-a-trait idea
        // - maybe this thing is arbitrary/uninterpreted with some admit()s?
        // - can this thing be an ISet::new.to_finite()?
        //  but we don't know whether we're supposed to be calling to_finite.
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
        }
    }

    /// Returns the number of key-value pairs in the map
    pub open spec fn len(self) -> nat {
        self.dom().len()
    }

    // TODO(jonh): discuss: I moved union, remove_keys (difference), and restrict (intersect) into
    // here because now they're doing trusted construction (because of the Finite=true soundness
    // case.)

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
    // TODO(jonh): I 'closed' this definition, which means I'll need to expose it another way.
    pub closed spec fn union_prefer_right(self, m2: Self) -> Self {
        Self{
            mapping: |k: K| if self.dom().contains(k) || m2.dom().contains(k) {
                Some(
                    if m2.dom().contains(k) {
                        m2[k]
                    } else {
                        self[k]
                    }
                ) } else { None }
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
    pub closed spec fn remove_keys(self, keys: GSet<K, Finite>) -> Self {
        Self{
            mapping: |k: K| if self.dom().contains(k) && !keys.contains(k) { Some(self[k]) } else { None }
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
    pub closed spec fn restrict(self, keys: GSet<K, Finite>) -> Self {
        Self{
            mapping: |k: K| if self.dom().contains(k) && keys.contains(k) { Some(self[k]) } else { None }
        }
    }

    // TODO(jonh): expose as broadcast lemmas
    pub proof fn lemma_union_prefer_right(self, m2: Self)
    ensures
        self.union_prefer_right(m2).dom().to_infinite() == self.dom().union(m2.dom()),
        forall |k| #![auto] self.union_prefer_right(m2).dom().contains(k) ==>
            self.union_prefer_right(m2)[k] == if m2.dom().contains(k) { m2[k] } else { self[k] },
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // TODO(verus): trigger extn
        assert( self.union_prefer_right(m2).dom().to_infinite() == self.dom().union(m2.dom()) );
    }

    pub proof fn lemma_remove_keys(self, keys: GSet<K, Finite>)
    ensures
        self.remove_keys(keys).dom().to_infinite() == self.dom().difference(keys),
        forall |k| #![auto] self.remove_keys(keys).dom().contains(k) ==> self.remove_keys(keys)[k] == self[k]
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn
        assert( self.remove_keys(keys).dom().to_infinite() == self.dom().difference(keys) );
    }

    pub proof fn lemma_restrict(self, keys: GSet<K, Finite>)
    ensures
        self.restrict(keys).dom().to_infinite() == self.dom().intersect(keys),
        forall |k| #![auto] self.restrict(keys).dom().contains(k) ==> self.restrict(keys)[k] == self[k]
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn
        assert( self.restrict(keys).dom().to_infinite() == self.dom().intersect(keys) );
    }

    /// Map a function `f` over all (k, v) pairs in `self`.
    pub closed spec fn map_entries<W>(self, f: spec_fn(K, V) -> W) -> GMap<K, W, Finite> {
        GMap {
            mapping: |k| if self.contains_key(k) { Some(f(k, self[k])) } else { None }
        }
    }

    pub proof fn lemma_map_entries<W>(self, f: spec_fn(K, V) -> W)
    ensures
        self.map_entries(f).dom() == self.dom(),
        forall |k| #![auto] self.map_entries(f).contains_key(k) ==> self.map_entries(f)[k] == f(k, self[k]),
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn
        assert( self.map_entries(f).dom() == self.dom() );
    }

    /// Map a function `f` over the values in `self`.
    pub closed spec fn map_values<W>(self, f: spec_fn(V) -> W) -> GMap<K, W, Finite> {
        GMap {
            mapping: |k| if self.contains_key(k) { Some(f(self[k])) } else { None }
        }
    }

    pub proof fn lemma_map_values<W>(self, f: spec_fn(V) -> W)
    ensures
        self.map_values(f).dom() == self.dom(),
        forall |k| #![auto] self.map_values(f).contains_key(k) ==> self.map_values(f)[k] == f(self[k]),
    {
        broadcast use super::set::group_set_lemmas;
        broadcast use axiom_dom_ensures;
        // trigger extn
        assert( self.map_values(f).dom() == self.dom() );
    }

    /// Swaps map keys and values. Values are not required to be unique; no
    /// promises on which key is chosen on the intersection.
    pub closed spec fn invert(self) -> Map<V, K> {
        GMap {
            mapping: |v| if self.contains_value(v) { Some(choose|k: K| self.contains_pair(k, v)) } else { None }
        }
    }

    #[verifier::external_body]
    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == GMap::<K, V, Finite>::empty(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == Self::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    /// todo fill in documentation
    #[verifier::external_body]
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == Self::remove(*old(self), key),
            v == old(self)[key],
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_borrow(tracked &self, key: K) -> (tracked v: &V)
        requires
            self.dom().contains(key),
        ensures
            *v === self.index(key),
    {
        unimplemented!();
    }

    // TODO(jonh): (discuss) This soundly preserves finiteness because it is doing set
    // mapping, which preserves finiteness.
    #[verifier::external_body]
    pub proof fn tracked_map_keys<J>(
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
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_remove_keys(tracked &mut self, keys: GSet<K, Finite>) -> (tracked out_map: Self)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    {
        unimplemented!();
    }

    // TODO(jonh): introduce union and finite_union? This one requires right to match in
    // finiteness, so it's not a general union like we have in the set library.
    // TODO(jonh): ew yuck this depends on map_lib::union_prefer_right. How is that even legal?
    #[verifier::external_body]
    pub proof fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    {
        unimplemented!();
    }
}

// TODO(jonh): broadcast -- but only meaningful internally
broadcast proof fn axiom_dom_ensures<K,V,const Finite: bool>(m: GMap<K,V,Finite>)
ensures congruent(#[trigger] m.dom(), ISet::new(|k| (m.mapping)(k) is Some))
{
    // This property relies on this module only allowing the construction of
    // finite mappings inside GMaps with Finite=true.
    admit();
}


impl<K, V> Map<K, V> {
    // Preserves finite soundness because key_set is finite by its type.
    pub closed spec fn new(key_set: Set<K>, fv: spec_fn(K) -> V) -> Map<K, V> {
        Map { mapping: |k| if key_set.contains(k) { Some(fv(k)) } else { None } }
    }
}

// TODO(verus): discuss why am I getting this warning?
// warning: broadcast functions should have explicit #[trigger] or #![trigger ...]
pub broadcast proof fn lemma_finite_new_ensures<K,V>(key_set: Set<K>, fv: spec_fn(K) -> V)
    ensures
    // well this trigger is obviously broken
        forall |k| key_set.contains(k) <==> (#[trigger] Map::new(key_set, fv)).dom().contains(k),
        forall |k| key_set.contains(k) ==> Map::new(key_set, fv)[k] == fv(k),

// ugh but when I try to write sensical triggers, I get myself into an error. Halp.
// TODO(verus): trigger group 0 does not cover variable k
//         forall |k| #![trigger Map::new(key_set, fv).dom().contains(k)] key_set.contains(k) <==> Map::new(key_set, fv).dom().contains(k),
//         forall |k| #![trigger Map::new(key_set, fv)[k]] key_set.contains(k) ==> Map::new(key_set, fv)[k] == fv(k),
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
    // TODO(jonh): broadcast lemma to export meaning of this new expression.
    pub closed spec fn new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V) -> IMap<K, V> {
        IMap { mapping: |k| if fk(k) { Some(fv(k)) } else { None } }
    }
}

pub broadcast proof fn lemma_infinite_new_ensures<K,V>(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V)
    ensures
        forall |k| fk(k) <==> (#[trigger] IMap::new(fk, fv)).dom().contains(k),
        forall |k| fk(k) ==> IMap::new(fk, fv)[k] == fv(k),
{
    broadcast use super::set::group_set_lemmas;
    broadcast use axiom_dom_ensures;
}

// Trusted axioms
/* REVIEW: this is simpler than the two separate axioms below -- would this be ok?
pub broadcast proof fn axiom_map_index_decreases<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key])),
{
    admit();
}
*/

pub broadcast proof fn axiom_map_index_decreases_finite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
{
    admit();
}

// REVIEW: this is currently a special case that is hard-wired into the verifier
// It implements a version of https://github.com/FStarLang/FStar/pull/2954 .
pub broadcast proof fn axiom_map_index_decreases_infinite<K, V>(m: Map<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
{
    admit();
}

/// The domain of the empty map is the empty set
pub broadcast proof fn axiom_map_empty<K, V, const Finite: bool>()
    ensures
        #[trigger] GMap::<K, V, Finite>::empty().dom() == GSet::<K, Finite>::empty(),
{
    broadcast use super::set::group_set_lemmas;

    broadcast use axiom_dom_ensures;
//     GMap::<K, V, Finite>::empty().axiom_dom_ensures();

    // TODO(jonh): discuss with Chris -- trigger extn since ensures refuses to do so
    assert( GMap::<K, V, Finite>::empty().dom() == GSet::<K, Finite>::empty() );
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
pub broadcast proof fn axiom_map_insert_domain<K, V, const Finite: bool>(m: GMap<K, V, Finite>, key: K, value: V)
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
pub broadcast proof fn axiom_map_insert_same<K, V, const Finite: bool>(m: GMap<K, V, Finite>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
pub broadcast proof fn axiom_map_insert_different<K, V, const Finite: bool>(m: GMap<K, V, Finite>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
pub broadcast proof fn axiom_map_remove_domain<K, V, const Finite: bool>(m: GMap<K, V, Finite>, key: K)
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
pub broadcast proof fn axiom_map_remove_different<K, V, const Finite: bool>(m: GMap<K, V, Finite>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
pub broadcast proof fn axiom_map_ext_equal<K, V, const Finite: bool>(m1: GMap<K, V, Finite>, m2: GMap<K, V, Finite>)
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

pub broadcast proof fn axiom_map_ext_equal_deep<K, V, const Finite: bool>(m1: GMap<K, V, Finite>, m2: GMap<K, V, Finite>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    axiom_map_ext_equal(m1, m2);
}

pub broadcast group group_map_axioms {
//     TODO(verus): discuss shouldn't be able to broadcast this since its ensures
//     talks about .mapping field?
//     axiom_dom_ensures,
    lemma_finite_new_ensures,
    lemma_infinite_new_ensures,
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
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V, const Finite: bool>(m: GMap<K, V, Finite>) -> GMap<K, V, Finite> {
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
