#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[cfg(verus_keep_ghost)]
use super::std_specs::borrow::BorrowSpec;
#[cfg(verus_keep_ghost)]
use super::std_specs::cmp::{PartialEqSpec, eq_matches_view_equality};
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::{hash_map_keys_differ, obeys_key_model};
#[cfg(verus_keep_ghost)]
use super::std_specs::iter::IteratorSpec;
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashMap;

verus! {

broadcast use {
    crate::map::group_map_lemmas,
    crate::set::group_set_lemmas,
    crate::set::Set::lemma_map_contains,
    crate::seq::group_seq_axioms,
    crate::seq_lib::lemma_seq_contains,
    crate::seq_lib::group_seq_lib_default,
    crate::std_specs::hash::group_hash_axioms,
    crate::std_specs::borrow::group_borrow_axioms,
};

/// `HashMapWithView` is a verified wrapper around `std::collections::HashMap` with `View` implemented for the type `vstd::map::Map<<Key as View>::V, Value>`.
///
/// Its constructors require [`eq_matches_view_equality`] in addition to [`obeys_key_model`].
/// Constructors establish [`Self::well_formed`], which all other operations require and preserve.
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

    closed spec fn view(&self) -> Self::V {
        Map::new(
            self.m@.dom().map(|k: Key| k@),
            |view: Key::V| self.m@[choose|k: Key| #[trigger] self.m@.contains_key(k) && k@ == view],
        )
    }
}

impl<Key, Value> HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    pub closed spec fn well_formed(&self) -> bool {
        &&& obeys_key_model::<Key>()
        &&& eq_matches_view_equality::<Key>()
        &&& hash_map_keys_differ(&self.m)
    }

    proof fn lemma_view(&self)
        requires
            self.well_formed(),
        ensures
            self@.len() == self.m@.len(),
            forall|k: Key| #[trigger]
                self.m@.contains_key(k) ==> self@.contains_key(k@) && self@[k@] == self.m@[k],
            forall|view: Key::V| #[trigger]
                self@.contains_key(view) ==> exists|k: Key| #[trigger]
                    self.m@.contains_key(k) && k@ == view,
    {
        broadcast use {crate::map::group_map_lemmas, crate::set::group_set_lemmas};

        assert(self.m@.dom().injective_on(|k: Key| k@));
        crate::set_lib::lemma_map_size(self.m@.dom(), self.m@.dom().map(|k: Key| k@), |k: Key| k@);
        assert forall|k: Key| #[trigger] self.m@.contains_key(k) implies self@.contains_key(k@)
            && self@[k@] == self.m@[k] by {
            let other = choose|other: Key| #[trigger] self.m@.contains_key(other) && other@ == k@;
            assert(other == k);
        }
    }

    /// Creates an empty `HashMapWithView` with a capacity of 0.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            eq_matches_view_equality::<Key>(),
        ensures
            result.well_formed(),
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    /// Creates an empty `HashMapWithView` with at least capacity for the specified number of elements.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            eq_matches_view_equality::<Key>(),
        ensures
            result.well_formed(),
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    pub fn reserve(&mut self, additional: usize)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional)
    }

    /// Returns true if the map is empty.
    pub fn is_empty(&self) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.is_empty(),
    {
        proof {
            self.lemma_view();
        }
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    /// Returns the number of elements in the map.
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        requires
            self.well_formed(),
        ensures
            result == self@.len(),
    {
        proof {
            self.lemma_view();
        }
        self.m.len()
    }

    /// Inserts the given key and value in the map, returning the previous value if the key was present.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    pub fn insert(&mut self, k: Key, v: Value) -> (previous: Option<Value>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.insert(k@, v),
            previous == old(self)@.get(k@),
    {
        proof {
            self.lemma_view();
        }
        let ghost before = self@;
        let ghost old_m = self.m@;
        let previous = self.m.insert(k, v);
        proof {
            self.lemma_view();
            let stored_key = match &previous {
                Some(old_value) => choose|stored: Key|
                    {
                        &&& #[trigger] old_m.contains_key(stored)
                        &&& k.eq_spec(&stored)
                        &&& *old_value == old_m[stored]
                        &&& self.m@ == old_m.insert(stored, v)
                    },
                None => k,
            };
            assert(stored_key@ == k@);
            assert(self.m@.contains_key(stored_key));
            assert_maps_equal!(self@, before.insert(k@, v), view => {
                if view == k@ {
                    assert(self@.contains_key(view));
                    assert(self@[view] == v);
                } else if self@.contains_key(view) {
                    let stored = choose|stored: Key|
                        #[trigger] self.m@.contains_key(stored) && stored@ == view;
                    assert(old_m.contains_key(stored));
                    assert(before.contains_key(view));
                    assert(self@[view] == before[view]);
                }
                if before.contains_key(view) && view != k@ {
                    let stored = choose|stored: Key|
                        #[trigger] old_m.contains_key(stored) && stored@ == view;
                    assert(self.m@.contains_key(stored));
                    assert(self@.contains_key(view));
                }
            });
        }
        previous
    }

    /// Removes the given key from the map and returns the value. If the key is not present in the map, returns `None`
    /// and the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    pub fn remove(&mut self, k: &Key) -> (out: Option<Value>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            match out {
                Some(v) => old(self)@.contains_key(k@) && v == old(self)@[k@] && final(self)@
                    == old(self)@.remove(k@),
                None => !old(self)@.contains_key(k@) && final(self)@ == old(self)@,
            },
    {
        proof {
            self.lemma_view();
        }
        let ghost before = self@;
        let ghost old_m = self.m@;
        let out = self.m.remove(k);
        proof {
            self.lemma_view();
            if out is Some {
                assert_maps_equal!(self@, before.remove(k@), view => {
                    if self@.contains_key(view) {
                        let stored = choose|stored: Key|
                            #[trigger] self.m@.contains_key(stored) && stored@ == view;
                        assert(view != k@);
                    }
                    if before.contains_key(view) && view != k@ {
                        let stored = choose|stored: Key|
                            #[trigger] old_m.contains_key(stored) && stored@ == view;
                        assert(self.m@.contains_key(stored));
                    }
                });
            }
        }
        out
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    pub fn contains_key(&self, k: &Key) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.contains_key(k@),
    {
        proof {
            self.lemma_view();
        }
        self.m.contains_key(k)
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
        requires
            self.well_formed(),
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        proof {
            self.lemma_view();
        }
        self.m.get(k)
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    pub fn clear(&mut self)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == Map::<<Key as View>::V, Value>::empty(),
    {
        self.m.clear();
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    pub fn union_prefer_right(&mut self, other: Self)
        requires
            old(self).well_formed(),
            other.well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.union_prefer_right(other@),
    {
        proof {
            self.lemma_view();
            other.lemma_view();
        }
        let ghost target = self@.union_prefer_right(other@);
        let ghost other_view = other@;
        let ghost other_map = other.m@;
        let mut iter = other.m.into_iter();
        proof {
            assert(iter.remaining().to_set() == other_map.kv_pairs());
            assert forall|i: int| 0 <= i < iter.remaining().len() implies other_view.contains_key(
                #[trigger] iter.remaining()[i].0@,
            ) && other_view[iter.remaining()[i].0@] == iter.remaining()[i].1 by {
                let pair = iter.remaining()[i];
                assert(iter.remaining().to_set().contains(pair));
                assert(other_map.contains_key(pair.0));
            }
            assert forall|view: Key::V| #[trigger] target.contains_key(view) implies (
            self@.contains_key(view) && self@[view] == target[view]) || exists|i: int|
                0 <= i < iter.remaining().len() && #[trigger] iter.remaining()[i].0@ == view by {
                if other_view.contains_key(view) {
                    let key = choose|key: Key| #[trigger]
                        other_map.contains_key(key) && key@ == view;
                    assert(other_map.kv_pairs().contains((key, other_map[key])));
                    assert(iter.remaining().to_set().contains((key, other_map[key])));
                    assert(iter.remaining().contains((key, other_map[key])));
                    let i = choose|i: int|
                        0 <= i < iter.remaining().len() && #[trigger] iter.remaining()[i] == (
                            key,
                            other_map[key],
                        );
                    assert(iter.remaining()[i].0@ == view);
                }
            }
        }
        loop
            invariant
                self.well_formed(),
                iter.decrease() is Some,
                target == old(self)@.union_prefer_right(other@),
                other_view.submap_of(target),
                forall|view: Key::V| #[trigger]
                    self@.contains_key(view) ==> target.contains_key(view),
                forall|view: Key::V| #[trigger]
                    target.contains_key(view) ==> (self@.contains_key(view) && self@[view]
                        == target[view]) || exists|i: int|
                        0 <= i < iter.remaining().len() && #[trigger] iter.remaining()[i].0@
                            == view,
                forall|i: int|
                    0 <= i < iter.remaining().len() ==> other_view.contains_key(
                        #[trigger] iter.remaining()[i].0@,
                    ) && other_view[iter.remaining()[i].0@] == iter.remaining()[i].1,
            decreases iter.decrease()->0,
        {
            #[verifier::prophetic]
            let ghost remaining = iter.remaining();
            let ghost before = self@;
            match iter.next() {
                Some((key, value)) => {
                    self.insert(key, value);
                    proof {
                        assert forall|view: Key::V| #[trigger] target.contains_key(view) implies (
                        self@.contains_key(view) && self@[view] == target[view]) || exists|i: int|
                            0 <= i < iter.remaining().len() && #[trigger] iter.remaining()[i].0@
                                == view by {
                            if !(self@.contains_key(view) && self@[view] == target[view]) {
                                assert(!(before.contains_key(view) && before[view]
                                    == target[view]));
                                let i = choose|i: int|
                                    0 <= i < remaining.len() && #[trigger] remaining[i].0@ == view;
                                assert(i > 0);
                                assert(iter.remaining()[i - 1].0@ == view);
                            }
                        }
                    }
                },
                None => {
                    proof {
                        assert(iter.remaining().len() == 0);
                        assert(self@ =~= target);
                    }
                    return;
                },
            }
        }
    }
}

/// `StringHashMap` is a verified wrapper around `std::collections::HashMap<String, Value>` with `View` implemented for the type `vstd::map::Map<Seq<char>, Value>`.
///
/// This type was created for ease of use with `String` as it uses `&str` instead of `&String` for methods that require shared references.
/// Constructors establish [`Self::well_formed`], which all other operations require and preserve.
/// Standard-library axioms provide the key models for `String` and `str`.
///
/// See the Rust documentation for [`HashMap`](https://doc.rust-lang.org/std/collections/struct.HashMap.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashMap` directly, see [`ExHashMap`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashMap.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
pub struct StringHashMap<Value> {
    m: HashMapWithView<String, Value>,
}

impl<Value> View for StringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    closed spec fn view(&self) -> Self::V {
        self.m@
    }
}

impl<Value> StringHashMap<Value> {
    pub closed spec fn well_formed(&self) -> bool {
        self.m.well_formed()
    }

    /// Creates an empty `StringHashMap` with a capacity of 0.
    ///
    /// See Rust's [`HashMap::new()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.new) for implementation details.
    pub fn new() -> (result: Self)
        ensures
            result.well_formed(),
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMapWithView::new() }
    }

    /// Creates an empty `StringHashMap` with at least capacity for the specified number of elements.
    ///
    /// See Rust's [`HashMap::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.with_capacity) for implementation details.
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result.well_formed(),
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMapWithView::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the map.
    ///
    /// See Rust's [`HashMap::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.reserve) for implementation details.
    pub fn reserve(&mut self, additional: usize)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the map is empty.
    pub fn is_empty(&self) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the map.
    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    /// Returns the number of elements in the map.
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        requires
            self.well_formed(),
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given key and value in the map, returning the previous value if the key was present.
    ///
    /// See Rust's [`HashMap::insert()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.insert) for implementation details.
    pub fn insert(&mut self, k: String, v: Value) -> (previous: Option<Value>)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.insert(k@, v),
            previous == old(self)@.get(k@),
    {
        self.m.insert(k, v)
    }

    /// Removes the given key from the map. If the key is not present in the map, the map is unmodified.
    ///
    /// See Rust's [`HashMap::remove()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.remove) for implementation details.
    pub fn remove(&mut self, k: &str)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.remove(k@),
    {
        proof {
            self.m.lemma_view();
        }
        let ghost before = self@;
        let ghost old_m = self.m.m@;
        let out = self.m.m.remove(k);
        proof {
            self.m.lemma_view();
            if out is None && before.contains_key(k@) {
                let stored = choose|stored: String| #[trigger]
                    old_m.contains_key(stored) && stored@ == k@;
                assert(k.eq_spec(<String as BorrowSpec<str>>::borrow_spec(&stored)));
            }
            assert_maps_equal!(self@, before.remove(k@), view => {
                if self@.contains_key(view) {
                    let stored = choose|stored: String| #[trigger]
                        self.m.m@.contains_key(stored) && stored@ == view;
                    assert(view != k@);
                }
                if before.contains_key(view) && view != k@ {
                    let stored = choose|stored: String| #[trigger]
                        old_m.contains_key(stored) && stored@ == view;
                    assert(self.m.m@.contains_key(stored));
                }
            });
        }
    }

    /// Returns true if the map contains the given key.
    ///
    /// See Rust's [`HashMap::contains_key()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.contains_key) for implementation details.
    pub fn contains_key(&self, k: &str) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.contains_key(k@),
    {
        self.get(k).is_some()
    }

    /// Returns a reference to the value corresponding to the given key in the map. If the key is not present in the map, returns `None`.
    ///
    /// See Rust's [`HashMap::get()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get) for implementation details.
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a Value>)
        requires
            self.well_formed(),
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        proof {
            self.m.lemma_view();
        }
        let result = self.m.m.get(k);
        proof {
            match result {
                Some(value) => {
                    let stored = choose|stored: String|
                        {
                            &&& #[trigger] self.m.m@.contains_key(stored)
                            &&& k.eq_spec(<String as BorrowSpec<str>>::borrow_spec(&stored))
                            &&& self.m.m@[stored] == *value
                        };
                    assert(stored@ == k@);
                },
                None => {
                    if self@.contains_key(k@) {
                        let stored = choose|stored: String| #[trigger]
                            self.m.m@.contains_key(stored) && stored@ == k@;
                        assert(k.eq_spec(<String as BorrowSpec<str>>::borrow_spec(&stored)));
                    }
                },
            }
        }
        result
    }

    /// Clears all key-value pairs in the map. Retains the allocated memory for reuse.
    ///
    /// See Rust's [`HashMap::clear()`](https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.clear) for implementation details.
    pub fn clear(&mut self)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == Map::<Seq<char>, Value>::empty(),
    {
        self.m.clear()
    }

    /// Returns the union of the two maps. If a key is present in both maps, then the value in the right map (`other`) is retained.
    pub fn union_prefer_right(&mut self, other: Self)
        requires
            old(self).well_formed(),
            other.well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.union_prefer_right(other@),
    {
        self.m.union_prefer_right(other.m)
    }
}

} // verus!
