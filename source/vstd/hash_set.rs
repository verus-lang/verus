// altered from HashMap
use core::marker;
use std::borrow::Borrow;

#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[allow(unused_imports)]
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::obeys_key_model;
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashSet;

verus! {

/// `HashSetWithView` is a trusted wrapper around `std::collections::HashSet` with `View` implemented for the type `vstd::map::Set<<Key as View>::V>`.
///
/// See the Rust documentation for [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
/// for details about the implementation.
///
/// If you are using `std::collections::HashSet` directly, see [`ExHashSet`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashSet.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
pub struct HashSetWithView<Key> where Key: View + Eq + Hash {
    m: HashSet<Key>,
}

impl<Key> View for HashSetWithView<Key> where Key: View + Eq + Hash {
    type V = Set<<Key as View>::V>;

    uninterp spec fn view(&self) -> Self::V;
}

impl<Key> HashSetWithView<Key> where Key: View + Eq + Hash {
    /// Creates an empty `HashSet` with capacity 0.
    // todo - key model
    /// See Rust's [`HashSet::new()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.new).
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::new() }
    }

    /// Creates an empty `HashSet` with at least capacity for the specified number of elements.
    /// See Rust's [`HashSet::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.with_capacity).
    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the set.
    /// See Rust's [`HashSet::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.reserve).
    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns the number of elements in the set.
    pub uninterp spec fn spec_len(&self) -> usize;

    /// Returns the number of elements in the set.
    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Returns true if the set is empty.
    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Inserts the given value into the set. Returns true if the value was previously in the set, false otherwise.
    /// See Rust's [`HashSet::insert()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.insert).
    #[verifier::external_body]
    pub fn insert(&mut self, k: Key) -> (result: bool)
        ensures
            self@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    /// Removes the given value from the set. Returns true if the value was previously in the set, false otherwise.
    /// See Rust's [`HashSet::remove()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.remove).
    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (result: bool)
        ensures
            self@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        self.m.remove(k)
    }

    /// Returns true if the set contains the given value.
    /// See Rust's [`HashSet::contains()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.contains).
    #[verifier::external_body]
    pub fn contains(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains(k@),
    {
        self.m.contains(k)
    }

    /// Returns a reference to the value in the set that is equal to the given value. If the value is not present in the set, returns `None`.
    /// See Rust's [`HashSet::get()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.get).
    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Key>)
        ensures
            match result {
                Some(v) => self@.contains(k@) && v == &k,
                None => !self@.contains(k@),
            },
    {
        self.m.get(k)
    }

    /// Clears all values from the set.
    /// See Rust's [`HashSet::clear()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.clear).
    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Set::<<Key as View>::V>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast axiom fn axiom_hash_set_with_view_spec_len<Key>(m: &HashSetWithView<Key>) where
    Key: View + Eq + Hash,

    ensures
        #[trigger] m.spec_len() == m@.len(),
;

#[verifier::ext_equal]
pub struct StringHashSet {
    m: HashSet<String>,
}

impl View for StringHashSet {
    type V = Set<Seq<char>>;

    uninterp spec fn view(&self) -> Self::V;
}

impl StringHashSet {
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSet::new() }
    }

    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSet::with_capacity(capacity) }
    }

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    #[verifier::external_body]
    pub fn is_empty(&self) -> (result: bool)
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    pub uninterp spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: String) -> (result: bool)
        ensures
            self@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &str) -> (result: bool)
        ensures
            self@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        self.m.remove(k)
    }

    #[verifier::external_body]
    pub fn contains(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains(k@),
    {
        self.m.contains(k)
    }

    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a String>)
        ensures
            match result {
                Some(v) => self@.contains(k@) && v@ == k@,
                None => !self@.contains(k@),
            },
    {
        self.m.get(k)
    }

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Set::<Seq<char>>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast axiom fn axiom_string_hash_set_spec_len(m: &StringHashSet)
    ensures
        #[trigger] m.spec_len() == m@.len(),
;

pub broadcast group group_hash_set_axioms {
    axiom_hash_set_with_view_spec_len,
    axiom_string_hash_set_spec_len,
}

} // verus!
