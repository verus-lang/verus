#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

verus2! {

/// `Map<K, V>` is an abstract map type for specifications.
/// To use a "map" in compiled code, use an `exec` type like HashMap (TODO)
/// that has a `Map<K, V>` as its specification type.
///
/// An object `map: Map<K, V>` has a _domain_, a set of keys given by [`map.dom()`](Map::dom),
/// and a mapping for keys in the domain to values, given by [`map.index(key)`](Map::index).
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
pub tracked struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
    dummy: std::marker::PhantomData<(K, V)>,
}

impl<K, V> Map<K, V> {
    pub spec fn empty() -> Map<K, V>;

    /// Gives a `Map<K, V>` whose domain contains every key, and maps each key
    /// to the value given by `fv`.

    pub open spec fn total<F: Fn(K) -> V>(fv: F) -> Map<K, V> {
        Set::full().mk_map(fv)
    }

    /// Gives a `Map<K, V>` whose domain is given by the boolean predicate on keys `fk`,
    /// and maps each key to the value given by `fv`.

    pub open spec fn new<FK: Fn(K) -> bool, FV: Fn(K) -> V>(fk: FK, fv: FV) -> Map<K, V> {
        Set::new(fk).mk_map(fv)
    }

    /// The domain of the map as a set.

    pub spec fn dom(self) -> Set<K>;

    /// Gets the value that the given key `key` maps to.
    /// For keys not in the domain, the result is meaningless and arbitrary.

    pub spec fn index(self, key: K) -> V
        recommends self.dom().contains(key);

    /// Inserts the given (key, value) pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.

    pub spec fn insert(self, key: K, value: V) -> Map<K, V>;

    /// Removes the given key and its associated value from the map.
    ///
    /// If the key is already absent from the map, then the map is left unchanged.

    pub spec fn remove(self, key: K) -> Map<K, V>;

    /// Returns true if the two maps are pointwise equal, i.e.,
    /// they have the same domains and the corresponding values are equal
    /// for each key. This is equivalent to the maps being actually equal
    /// by [`axiom_map_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it is generally easier
    /// to use the [`assert_maps_equal!`] macro, rather than using `ext_equal` directly.

    pub open spec fn ext_equal(self, m2: Map<K, V>) -> bool {
        &&& self.dom().ext_equal(m2.dom())
        &&& (forall|k: K| #![auto] self.dom().contains(k) ==> self.index(k) === m2.index(k))
    }

    /// Returns true if the key `k` is in the domain of `self`, and it maps to the value `v`.

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && self.index(k) === v
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
            #[trigger] m2.dom().contains(k) && self.index(k) === m2.index(k)
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
            |k: K| if m2.dom().contains(k) { m2.index(k) } else { self.index(k) }
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
            |k: K| self.index(k)
        )
    }

    /// Returns `true` if the two given maps agree on all keys that their domains
    /// share in common.

    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==>
            self.index(k) === m2.index(k)
    }

    #[verifier(external_body)]
    pub proof fn proof_empty() -> (tracked out_v: Self)
        ensures
            out_v === Map::empty(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn proof_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self === Map::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn proof_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self === Map::remove(*old(self), key),
            v === old(self).index(key),
    {
        unimplemented!();
    }
}

// Trusted axioms

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() === Set::empty(),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() === m.dom().insert(key),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).index(key) === value,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        m.dom().contains(key1),
        key1 !== key2,
    ensures
        m.insert(key2, value).index(key1) === m.index(key1),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() === m.dom().remove(key),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        m.dom().contains(key1),
        key1 !== key2,
    ensures
        m.remove(key2).index(key1) === m.index(key1),
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        m1.ext_equal(m2) == (m1 === m2),
{
}

// Macros

#[doc(hidden)]
#[macro_export]
macro_rules! map_insert_rec {
    [$val:expr;] => {
        $val
    };
    [$val:expr;$key:expr => $value:expr] => {
        map_insert_rec![$val.insert($key, $value);]
    };
    [$val:expr;$key:expr => $value:expr,$($tail:tt)*] => {
        map_insert_rec![$val.insert($key, $value);$($tail)*]
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::pervasive::map::map_insert_rec![$crate::pervasive::map::Map::empty();$($tail)*])
    }
} 

pub use map_insert_rec;
pub use map;

/// Prove two maps equal by _extensionality_. Usage is:
///
/// ```rust
/// assert_maps_equal!(map1, map2);
/// ```
/// 
/// or,
/// 
/// ```rust
/// assert_maps_equal!(map1, map2, k: Key => {
///     // proof goes here that `map1` and `map2` agree on key `k`,
///     // i.e., `k` is in the domain of `map`` iff it is in the domain of `map2`
///     // and if so, then their values agree.
/// });
/// ```

#[macro_export]
macro_rules! assert_maps_equal {
    ($m1:expr, $m2:expr $(,)?) => {
        assert_maps_equal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[spec] let m1 = $m1;
        #[spec] let m2 = $m2;
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                ::builtin::ensures([
                    ((#[trigger] m1.dom().contains($k)) >>= m2.dom().contains($k))
                    && (m2.dom().contains($k) >>= m1.dom().contains($k))
                    && (m1.dom().contains($k) && m2.dom().contains($k) >>=
                        ::builtin::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            $crate::pervasive::assert(m1.ext_equal(m2));
        });
    }
}

pub use assert_maps_equal;

} // verus!
