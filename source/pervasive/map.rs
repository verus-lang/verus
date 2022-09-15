#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;
use core::marker;

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
pub tracked struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
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

    /// Returns true if the two maps are pointwise equal, i.e.,
    /// they have the same domains and the corresponding values are equal
    /// for each key. This is equivalent to the maps being actually equal
    /// by [`axiom_map_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it is generally easier
    /// to use the [`assert_maps_equal!`] macro, rather than using `ext_equal` directly.

    pub open spec fn ext_equal(self, m2: Map<K, V>) -> bool {
        &&& self.dom().ext_equal(m2.dom())
        &&& (forall|k: K| #![auto] self.dom().contains(k) ==> self[k] === m2[k])
    }

    /// Returns true if the key `k` is in the domain of `self`, and it maps to the value `v`.

    pub open spec fn contains_pair(self, k: K, v: V) -> bool {
        self.dom().contains(k) && self[k] === v
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
            #[trigger] m2.dom().contains(k) && self[k] === m2[k]
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

    /// Returns `true` if the two given maps agree on all keys that their domains
    /// share in common.

    pub open spec fn agrees(self, m2: Self) -> bool {
        forall|k| #![auto] self.dom().contains(k) && m2.dom().contains(k) ==>
            self[k] === m2[k]
    }

    #[verifier(external_body)]
    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v === Map::empty(),
    {
        unimplemented!();
    }

    #[verifier(external_body)]
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self === Map::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    /// todo fill in documentation

    #[verifier(external_body)]
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self === Map::remove(*old(self), key),
            v === old(self)[key],
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
        #[trigger] m.insert(key, value)[key] === value,
{
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        m.dom().contains(key1),
        key1 !== key2,
    ensures
        m.insert(key2, value)[key1] === m[key1],
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
        m.remove(key2)[key1] === m[key1],
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
macro_rules! map_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::pervasive::map::Map::empty()
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::pervasive::map::map_internal!($($tail)*))
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
///  * If they contain `k` in their domains, then their values are equal (`map1.dom().contains(k) && map2.dom().contains(k) ==> map1[k] === map2[k]`)
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_maps_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn insert_remove(m: Map<int, int>, k: int, v: int)
///     requires !m.dom().contains(k)
///     ensures m.insert(k, v).remove(k) === m
/// {
///     let m2 = m.insert(k, v).remove(k);
///     assert_maps_equal!(m, m2);
///     assert(m === m2);
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
///     assert_maps_equal!(m1, m2, key => {
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::pervasive::map::assert_maps_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_maps_equal_internal {
    ($m1:expr, $m2:expr $(,)?) => {
        assert_maps_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[spec] let m1 = $crate::pervasive::map::check_argument_is_map($m1);
        #[spec] let m2 = $crate::pervasive::map::check_argument_is_map($m2);
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                // TODO better error message here: show the individual conjunct that fails,
                // and maybe give an error message in english as well
                ::builtin::ensures([
                    ::builtin::imply(#[trigger] m1.dom().contains($k), m2.dom().contains($k))
                    && ::builtin::imply(m2.dom().contains($k), m1.dom().contains($k))
                    && ::builtin::imply(m1.dom().contains($k) && m2.dom().contains($k),
                        ::builtin::equal(m1.index($k), m2.index($k)))
                ]);
                { $bblock }
            });
            $crate::pervasive::assert(m1.ext_equal(m2));
        });
    }
}

#[doc(hidden)]
pub use assert_maps_equal_internal;
pub use assert_maps_equal;

} // verus!
