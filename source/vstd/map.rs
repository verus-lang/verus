#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;
use super::set::*;
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
/// To prove that two maps are equal, it is usually easiest to use the extensionality operator `=~=`.
#[verifier::external_body]
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

    /// Gets the value that the given key `key` maps to.
    /// For keys not in the domain, the result is meaningless and arbitrary.
    pub spec fn index(self, key: K) -> V
        recommends
            self.dom().contains(key),
    ;

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
    pub spec fn insert(self, key: K, value: V) -> Map<K, V>;

    /// Removes the given key and its associated value from the map.
    ///
    /// If the key is already absent from the map, then the map is left unchanged.
    pub spec fn remove(self, key: K) -> Map<K, V>;

    /// Returns the number of key-value pairs in the map
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
    #[cfg_attr(not(verus_verify_core), deprecated = "use =~= or =~~= instead")]
    pub open spec fn ext_equal(self, m2: Map<K, V>) -> bool {
        self =~= m2
    }

    #[verifier::external_body]
    pub proof fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == Map::<K, V>::empty(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *self == Map::insert(*old(self), key, value),
    {
        unimplemented!();
    }

    /// todo fill in documentation
    #[verifier::external_body]
    pub proof fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *self == Map::remove(*old(self), key),
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
    pub proof fn tracked_remove_keys(tracked &mut self, keys: Set<K>) -> (tracked out_map: Map<
        K,
        V,
    >)
        requires
            keys.subset_of(old(self).dom()),
        ensures
            self == old(self).remove_keys(keys),
            out_map == old(self).restrict(keys),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn tracked_union_prefer_right(tracked &mut self, right: Self)
        ensures
            *self == old(self).union_prefer_right(right),
    {
        unimplemented!();
    }
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
pub broadcast proof fn axiom_map_empty<K, V>()
    ensures
        #[trigger] Map::<K, V>::empty().dom() == Set::<K>::empty(),
{
    admit();
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
pub broadcast proof fn axiom_map_insert_domain<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    admit();
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
pub broadcast proof fn axiom_map_insert_same<K, V>(m: Map<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
    admit();
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
pub broadcast proof fn axiom_map_insert_different<K, V>(m: Map<K, V>, key1: K, key2: K, value: V)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
    admit();
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
pub broadcast proof fn axiom_map_remove_domain<K, V>(m: Map<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    admit();
}

/// Removing a key-value pair from a map does not change the value mapped to by
/// any other keys in the map.
pub broadcast proof fn axiom_map_remove_different<K, V>(m: Map<K, V>, key1: K, key2: K)
    requires
        m.dom().contains(key1),
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
    admit();
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
pub broadcast proof fn axiom_map_ext_equal<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    admit();
}

pub broadcast proof fn axiom_map_ext_equal_deep<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    admit();
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
