use core::marker;

#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::obeys_key_model;
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashMap;

verus! {

/// `HashMapWithView` is a trusted wrapper around `std::collections::HashMap` with `View` implemented for the type `vstd::map::Map<<Key as View>::V, Value>`.
///
/// See the Rust documentation for [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashMap` directly, see [`ExHashMap`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashMap.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
pub struct HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    m: HashMap<Key, Value>,
}

impl<Key, Value> View for HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    type V = Map<<Key as View>::V, Value>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Key, Value> HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    /// Creates an empty `HashMapWithView` with a capacity of 0.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    /// Creates an empty `HashMapWithView` with at least capacity for the specified number of elements.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the map is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the map.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given key and value in the map.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: Key, v: Value)
        ensures
            self@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    /// Removes the given key from the map. If the key is not present in the map, the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key)
        ensures
            self@ == old(self)@.remove(k@),
    {
        self.m.remove(k);
    }

    /// Removes the given key from the map and returns the value. If the key is not present in the map, returns `None`
    /// and the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove_take(&mut self, k: &Key) -> (out: Option<Value>)
        ensures
            match out {
                Some(v) => old(self)@.contains_key(k@) && v == old(self)@[k@] && self@ == old(self)@.remove(k@),
                None => !old(self)@.contains_key(k@) && self@ == old(self)@,
            },
    {
        self.m.remove(k)
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    #[verifier::external_body]
    pub fn contains_key(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<<Key as View>::V, Value>::empty(),
    {
        self.m.clear()
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    #[verifier::external_body]
    pub fn union_prefer_right(&mut self, other: Self)
        ensures
            self@ == old(self)@.union_prefer_right(other@),
    {
        self.m.extend(other.m)
    }
}

pub broadcast axiom fn axiom_hash_map_with_view_spec_len<Key, Value>(
    m: &HashMapWithView<Key, Value>,
) where Key: View + Eq + Hash
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

/// `StringHashMap` is a trusted wrapper around `std::collections::HashMap<String, Value>` with `View` implemented for the type `vstd::map::Map<Seq<char>, Value>`.
///
/// This type was created for ease of use with `String` as it uses `&str` instead of `&String` for methods that require shared references.
/// Also, it assumes that [`obeys_key_model::<String>()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html) holds.
///
/// See the Rust documentation for [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashMap` directly, see [`ExHashMap`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashMap.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
pub struct StringHashMap<Value> {
    m: HashMap<String, Value>,
}

impl<Value> View for StringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Value> StringHashMap<Value> {
    /// Creates an empty `StringHashMap` with a capacity of 0.
    ///
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    /// Creates an empty `StringHashMap` with at least capacity for the specified number of elements.
    ///
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the map is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the map.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given key and value in the map.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    #[verifier::external_body]
    pub fn insert(&mut self, k: String, v: Value)
        ensures
            self@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    /// Removes the given key from the map. If the key is not present in the map, the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    #[verifier::external_body]
    pub fn remove(&mut self, k: &str)
        ensures
            self@ == old(self)@.remove(k@),
    {
        self.m.remove(k);
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    #[verifier::external_body]
    pub fn contains_key(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<Seq<char>, Value>::empty(),
    {
        self.m.clear()
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    #[verifier::external_body]
    pub fn union_prefer_right(&mut self, other: Self)
        ensures
            self@ == old(self)@.union_prefer_right(other@),
    {
        self.m.extend(other.m)
    }
}

pub broadcast axiom fn axiom_string_hash_map_spec_len<Value>(m: &StringHashMap<Value>)
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

pub broadcast group group_hash_map_axioms {
    axiom_hash_map_with_view_spec_len,
    axiom_string_hash_map_spec_len,
}

} // verus!
