#![allow(unused_imports)]

use super::pervasive::*;
use super::prelude::*;
use super::set::*;

use verus as verus_; // skip verusfmt due to unhandled return-value-pattern
verus_! {

/// `IMap<K, V>` is an abstract map type for specifications.
///
/// An object `map: IMap<K, V>` has a _domain_, a set of keys given by [`map.dom()`](IMap::dom),
/// and a mapping for keys in the domain to values, given by [`map[key]`](IMap::index).
/// Alternatively, a map can be thought of as a set of `(K, V)` pairs where each key
/// appears in at most entry.
///
/// In general, a map might be infinite.
/// To work specifically with finite maps, use `Map`.
///
/// IMaps can be constructed in a few different ways:
///  * [`IMap::empty()`] constructs an empty map.
///  * [`IMap::new`] and [`IMap::total`] construct a map given functions that specify its domain and the mapping
///     from keys to values (a _map comprehension_).
///  * The [`imap!`] macro, to construct small maps of a fixed size.
///  * By manipulating an existing map with [`IMap::insert`] or [`IMap::remove`].
///
/// To prove that two maps are equal, it is usually easiest to use the extensionality operator `=~=`.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(K)]
#[verifier::accept_recursive_types(V)]
pub tracked struct IMap<K, V> {
    mapping: spec_fn(K) -> Option<V>,
}

impl<K, V> IMap<K, V> {
    /// An empty map.
    pub closed spec fn empty() -> IMap<K, V> {
        IMap { mapping: |k| None }
    }

    /// Gives a `IMap<K, V>` whose domain contains every key, and maps each key
    /// to the value given by `fv`.
    pub open spec fn total(fv: spec_fn(K) -> V) -> IMap<K, V> {
        ISet::full().mk_map(fv)
    }

    /// Gives a `IMap<K, V>` whose domain is given by the boolean predicate on keys `fk`,
    /// and maps each key to the value given by `fv`.
    pub open spec fn new(fk: spec_fn(K) -> bool, fv: spec_fn(K) -> V) -> IMap<K, V> {
        ISet::new(fk).mk_map(fv)
    }

    /// The domain of the map as a set.
    pub closed spec fn dom(self) -> ISet<K> {
        ISet::new(|k| (self.mapping)(k) is Some)
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
    pub closed spec fn insert(self, key: K, value: V) -> IMap<K, V> {
        IMap {
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
    pub closed spec fn remove(self, key: K) -> IMap<K, V> {
        IMap {
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

    /// Create an empty tracked map.
    ///
    /// This allows us to create a map, which we know is empty, that is _tracked_.
    pub axiom fn tracked_empty() -> (tracked out_v: Self)
        ensures
            out_v == IMap::<K, V>::empty(),
    ;

    /// Inserts the given `(key, tracked value)` pair into the map.
    ///
    /// If the key is already present from the map, then its existing value is overwritten
    /// by the new value.
    pub axiom fn tracked_insert(tracked &mut self, key: K, tracked value: V)
        ensures
            *final(self) == IMap::insert(*old(self), key, value),
    ;

    /// Removes the given key and its associated _tracked_ value from the map.
    ///
    /// The key must exist in the map
    pub axiom fn tracked_remove(tracked &mut self, key: K) -> (tracked v: V)
        requires
            old(self).dom().contains(key),
        ensures
            *final(self) == IMap::remove(*old(self), key),
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
    pub axiom fn tracked_borrow_mut_split(tracked &mut self, keys: ISet<K>)
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
        tracked old_map: IMap<K, V>,
        key_map: IMap<J, K>,
    ) -> (tracked new_map: IMap<J, V>)
        requires
            forall|j| #![auto] key_map.contains_key(j) ==> old_map.contains_key(key_map[j]),
            forall|j1, j2|
                #![auto]
                j1 != j2 && key_map.contains_key(j1) && key_map.contains_key(j2) ==> key_map[j1]
                    != key_map[j2],
        ensures
            new_map.dom() == key_map.dom(),
            forall|j|
                key_map.contains_key(j) ==> new_map.contains_key(j) && #[trigger] new_map[j]
                    == old_map[key_map[j]],
    ;

    /// Extract a set of keys (and their corresponding values) out of the map.
    ///
    /// This allows us to split a map based on a subset of the domain.
    pub axiom fn tracked_remove_keys(tracked &mut self, keys: ISet<K>) -> (tracked out_map: IMap<
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
pub broadcast axiom fn axiom_imap_index_decreases<K, V>(m: IMap<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger](decreases_to!(m => m[key]));
*/

pub broadcast axiom fn axiom_imap_index_decreases_finite<K, V>(m: IMap<K, V>, key: K)
    requires
        m.dom().finite(),
        m.dom().contains(key),
    ensures
        #[trigger] (decreases_to!(m => m[key])),
;

// REVIEW: this is currently a special case that is hard-wired into the verifier
// It implements a version of https://github.com/FStarLang/FStar/pull/2954 .
pub broadcast axiom fn axiom_imap_index_decreases_infinite<K, V>(m: IMap<K, V>, key: K)
    requires
        m.dom().contains(key),
    ensures
        #[trigger] is_smaller_than_recursive_function_field(m[key], m),
;

/// The domain of the empty map is the empty set
pub broadcast proof fn lemma_imap_empty<K, V>()
    ensures
        #[trigger] IMap::<K, V>::empty().dom() == ISet::<K>::empty(),
{
    broadcast use super::iset::group_iset_lemmas;

    assert(ISet::new(|k: K| (|k| None::<V>)(k) is Some) == ISet::<K>::empty());
}

/// The domain of a map after inserting a key-value pair is equivalent to inserting the key into
/// the original map's domain set.
pub broadcast proof fn lemma_imap_insert_domain<K, V>(m: IMap<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value).dom() == m.dom().insert(key),
{
    broadcast use super::iset::group_iset_lemmas;

    assert(m.insert(key, value).dom() =~= m.dom().insert(key));
}

/// Inserting `value` at `key` in `m` results in a map that maps `key` to `value`
pub broadcast proof fn lemma_imap_insert_same<K, V>(m: IMap<K, V>, key: K, value: V)
    ensures
        #[trigger] m.insert(key, value)[key] == value,
{
}

/// Inserting `value` at `key2` does not change the value mapped to by any other keys in `m`
pub broadcast proof fn lemma_imap_insert_different<K, V>(m: IMap<K, V>, key1: K, key2: K, value: V)
    requires
        key1 != key2,
    ensures
        #[trigger] m.insert(key2, value)[key1] == m[key1],
{
}

/// The domain of a map after removing a key-value pair is equivalent to removing the key from
/// the original map's domain set.
pub broadcast proof fn lemma_imap_remove_domain<K, V>(m: IMap<K, V>, key: K)
    ensures
        #[trigger] m.remove(key).dom() == m.dom().remove(key),
{
    broadcast use super::iset::group_iset_lemmas;

    assert(m.remove(key).dom() =~= m.dom().remove(key));
}

/// Removing a key-value pair from a map does not change the value mapped to by
/// any other keys in the map.
pub broadcast proof fn lemma_imap_remove_different<K, V>(m: IMap<K, V>, key1: K, key2: K)
    requires
        key1 != key2,
    ensures
        #[trigger] m.remove(key2)[key1] == m[key1],
{
}

/// Two maps are equivalent if their domains are equivalent and every key in their domains map to the same value.
pub broadcast proof fn lemma_imap_ext_equal<K, V>(m1: IMap<K, V>, m2: IMap<K, V>)
    ensures
        #[trigger] (m1 =~= m2) <==> {
            &&& m1.dom() =~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] == m2[k]
        },
{
    broadcast use super::iset::group_iset_lemmas;

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

pub broadcast proof fn lemma_imap_ext_equal_deep<K, V>(m1: IMap<K, V>, m2: IMap<K, V>)
    ensures
        #[trigger] (m1 =~~= m2) <==> {
            &&& m1.dom() =~~= m2.dom()
            &&& forall|k: K| #![auto] m1.dom().contains(k) ==> m1[k] =~~= m2[k]
        },
{
    lemma_imap_ext_equal(m1, m2);
}

pub broadcast group group_imap_lemmas {
    axiom_imap_index_decreases_finite,
    axiom_imap_index_decreases_infinite,
    lemma_imap_empty,
    lemma_imap_insert_domain,
    lemma_imap_insert_same,
    lemma_imap_insert_different,
    lemma_imap_remove_domain,
    lemma_imap_remove_different,
    lemma_imap_ext_equal,
    lemma_imap_ext_equal_deep,
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! imap_internal {
    [$($key:expr => $value:expr),* $(,)?] => {
        $crate::vstd::imap::IMap::empty()
            $(.insert($key, $value))*
    }
}

/// Create a map using syntax like `imap![key1 => val1, key2 => val, ...]`.
///
/// This is equivalent to `IMap::empty().insert(key1, val1).insert(key2, val2)...`.
///
/// Note that this does _not_ require all keys to be distinct. In the case that two
/// or more keys are equal, the resulting map uses the value of the rightmost entry.
#[macro_export]
macro_rules! imap {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::imap::imap_internal!($($tail)*))
    };
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_map<K, V>(m: IMap<K, V>) -> IMap<K, V> {
    m
}

#[doc(hidden)]
pub use imap_internal;
pub use imap;

/// Prove two maps `map1` and `map2` are equal by proving that their values are equal at each key.
///
/// More precisely, `assert_imaps_equal!` requires that for each key `k`:
///  * `map1` contains `k` in its domain if and only if `map2` does (`map1.dom().contains(k) <==> map2.dom().contains(k)`)
///  * If they contain `k` in their domains, then their values are equal (`map1.dom().contains(k) && map2.dom().contains(k) ==> map1[k] == map2[k]`)
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_imaps_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn insert_remove(m: IMap<int, int>, k: int, v: int)
///     requires !m.dom().contains(k)
///     ensures m.insert(k, v).remove(k) == m
/// {
///     let m2 = m.insert(k, v).remove(k);
///     assert_imaps_equal!(m == m2);
///     assert(m == m2);
/// }
/// ```
///
/// For more complex cases, a proof may be required for each key:
///
/// ```rust
/// proof fn bitvector_maps() {
///     let m1 = IMap::<u64, u64>::new(
///         |key: u64| key & 31 == key,
///         |key: u64| key | 5);
///
///     let m2 = IMap::<u64, u64>::new(
///         |key: u64| key < 32,
///         |key: u64| 5 | key);
///
///     assert_imaps_equal!(m1 == m2, key => {
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
macro_rules! assert_imaps_equal {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::imap::assert_imaps_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_imaps_equal_internal {
    (::verus_builtin::spec_eq($m1:expr, $m2:expr)) => {
        assert_imaps_equal_internal!($m1, $m2)
    };
    (::verus_builtin::spec_eq($m1:expr, $m2:expr), $k:ident $( : $t:ty )? => $bblock:block) => {
        assert_imaps_equal_internal!($m1, $m2, $k $( : $t )? => $bblock)
    };
    ($m1:expr, $m2:expr $(,)?) => {
        assert_imaps_equal_internal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let m1 = $crate::vstd::imap::check_argument_is_map($m1);
        #[verifier::spec] let m2 = $crate::vstd::imap::check_argument_is_map($m2);
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
pub use assert_imaps_equal_internal;
pub use assert_imaps_equal;

} // verus!

verus_! { // skip verusfmt, issue with 'final'

impl<K, V> IMap<K, V> {
    pub proof fn tracked_map_keys_in_place(tracked &mut self, key_map: IMap<K, K>)
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
    {
        let tracked mut tmp = Self::tracked_empty();
        super::modes::tracked_swap(&mut tmp, self);
        let tracked mut tmp = Self::tracked_map_keys(tmp, key_map);
        super::modes::tracked_swap(&mut tmp, self);
    }
}

} // verus!
