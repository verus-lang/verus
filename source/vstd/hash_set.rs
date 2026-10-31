// altered from HashMap
use core::marker;
use std::borrow::Borrow;

#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[allow(unused_imports)]
use super::set::*;
#[cfg(verus_keep_ghost)]
use super::set_lib::assert_sets_equal;
#[cfg(verus_keep_ghost)]
use super::std_specs::borrow::BorrowSpec;
#[cfg(verus_keep_ghost)]
use super::std_specs::cmp::{PartialEqSpec, eq_matches_view_equality};
#[cfg(verus_keep_ghost)]
use super::std_specs::hash::{hash_set_inv, obeys_key_model};
#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashSet;

verus! {

broadcast use {
    crate::set::group_set_lemmas,
    crate::set::Set::lemma_map_contains,
    crate::set::Set::lemma_set_map_insert_commute,
    crate::std_specs::hash::group_hash_axioms,
    crate::std_specs::borrow::group_borrow_axioms,
};

/// `HashSetWithView` is a verified wrapper around `std::collections::HashSet` with `View` implemented for the type `vstd::set::Set<<Key as View>::V>`.
///
/// Its constructors require [`eq_matches_view_equality`] in addition to [`obeys_key_model`].
/// Constructors establish [`Self::well_formed`], which all other operations require and preserve.
///
/// See the Rust documentation for [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
/// for details about its implementation.
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

    closed spec fn view(&self) -> Self::V {
        self.m@.map(|k: Key| k@)
    }
}

impl<Key> HashSetWithView<Key> where Key: View + Eq + Hash {
    pub closed spec fn well_formed(&self) -> bool {
        &&& obeys_key_model::<Key>()
        &&& eq_matches_view_equality::<Key>()
        &&& hash_set_inv(&self.m)
    }

    proof fn lemma_view(&self)
        requires
            self.well_formed(),
        ensures
            self@.len() == self.m@.len(),
            forall|k: Key| #[trigger] self.m@.contains(k) ==> self@.contains(k@),
            forall|view: Key::V| #[trigger]
                self@.contains(view) ==> exists|k: Key| #[trigger]
                    self.m@.contains(k) && k@ == view,
    {
        assert(self.m@.injective_on(|k: Key| k@));
        crate::set_lib::lemma_map_size(self.m@, self@, |k: Key| k@);
    }

    /// Creates an empty `HashSetWithView`.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashSet::new()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.new) for implementation details.
    pub fn new() -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            eq_matches_view_equality::<Key>(),
        ensures
            result.well_formed(),
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::new() }
    }

    /// Creates an empty `HashSetWithView` with at least capacity for the specified number of elements.
    ///
    /// See [`obeys_key_model()`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/fn.obeys_key_model.html)
    /// for information on use with primitive types and other types.
    /// See Rust's [`HashSet::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.with_capacity) for implementation details.
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            obeys_key_model::<Key>(),
            eq_matches_view_equality::<Key>(),
        ensures
            result.well_formed(),
            result@ == Set::<<Key as View>::V>::empty(),
    {
        Self { m: HashSet::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the set.
    ///
    /// See Rust's [`HashSet::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.reserve) for implementation details.
    pub fn reserve(&mut self, additional: usize)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns the number of elements in the set.
    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    /// Returns the number of elements in the set.
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

    /// Returns true if the set is empty.
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

    /// Inserts the given value into the set. Returns true if the value was not previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::insert()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.insert) for implementation details.
    pub fn insert(&mut self, k: Key) -> (result: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        proof {
            self.lemma_view();
        }
        let result = self.m.insert(k);
        proof {
            self.lemma_view();
        }
        result
    }

    /// Removes the given value from the set. Returns true if the value was previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::remove()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.remove) for implementation details.
    pub fn remove(&mut self, k: &Key) -> (result: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        proof {
            self.lemma_view();
        }
        let ghost before = self@;
        let ghost old_m = self.m@;
        let result = self.m.remove(k);
        proof {
            self.lemma_view();
            if result {
                assert_sets_equal!(self@, before.remove(k@), view => {
                    if self@.contains(view) {
                        let stored = choose|stored: Key|
                            #[trigger] self.m@.contains(stored) && stored@ == view;
                        assert(view != k@);
                    }
                    if before.contains(view) && view != k@ {
                        let stored = choose|stored: Key|
                            #[trigger] old_m.contains(stored) && stored@ == view;
                        assert(self.m@.contains(stored));
                    }
                });
            }
        }
        result
    }

    /// Returns true if the set contains the given value.
    ///
    /// See Rust's [`HashSet::contains()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.contains) for implementation details.
    pub fn contains(&self, k: &Key) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.contains(k@),
    {
        proof {
            self.lemma_view();
        }
        self.m.contains(k)
    }

    /// Returns a reference to the value in the set that is equal to the given value. If the value is not present in the set, returns `None`.
    ///
    /// See Rust's [`HashSet::get()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.get) for implementation details.
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Key>)
        requires
            self.well_formed(),
        ensures
            match result {
                Some(v) => self@.contains(k@) && v@ == k@,
                None => !self@.contains(k@),
            },
    {
        proof {
            self.lemma_view();
        }
        self.m.get(k)
    }

    /// Clears all values from the set.
    ///
    /// See Rust's [`HashSet::clear()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.clear) for implementation details.
    pub fn clear(&mut self)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == Set::<<Key as View>::V>::empty(),
    {
        self.m.clear()
    }
}

/// `StringHashSet` is a verified wrapper around `std::collections::HashSet<String>` with `View` implemented for the type `vstd::set::Set<Seq<char>>`.
///
/// This type was created for ease of use with `String` as it uses `&str` instead of `&String` for methods that require shared references.
/// Constructors establish [`Self::well_formed`], which all other operations require and preserve.
/// Standard-library axioms provide the key models for `String` and `str`.
///
/// See the Rust documentation for [`HashSet`](https://doc.rust-lang.org/std/collections/struct.HashSet.html)
/// for details about its implementation.
///
/// If you are using `std::collections::HashSet` directly, see [`ExHashSet`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/hash/struct.ExHashSet.html)
/// for information on the Verus specifications for this type.
#[verifier::ext_equal]
pub struct StringHashSet {
    m: HashSetWithView<String>,
}

impl View for StringHashSet {
    type V = Set<Seq<char>>;

    closed spec fn view(&self) -> Self::V {
        self.m@
    }
}

impl StringHashSet {
    pub closed spec fn well_formed(&self) -> bool {
        self.m.well_formed()
    }

    /// Creates an empty `StringHashSet`.
    ///
    /// See Rust's [`HashSet::new()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.new) for implementation details.
    pub fn new() -> (result: Self)
        ensures
            result.well_formed(),
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSetWithView::new() }
    }

    /// Creates an empty `StringHashSet` with at least capacity for the specified number of elements.
    ///
    /// See Rust's [`HashSet::with_capacity()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.with_capacity) for implementation details.
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result.well_formed(),
            result@ == Set::<Seq<char>>::empty(),
    {
        Self { m: HashSetWithView::with_capacity(capacity) }
    }

    /// Reserves capacity for at least `additional` number of elements in the set.
    ///
    /// See Rust's [`HashSet::reserve()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.reserve) for implementation details.
    pub fn reserve(&mut self, additional: usize)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    /// Returns true if the set is empty.
    pub fn is_empty(&self) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.is_empty(),
    {
        self.m.is_empty()
    }

    /// Returns the number of elements in the set.
    pub open spec fn spec_len(&self) -> usize {
        self@.len() as usize
    }

    /// Returns the number of elements in the set.
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        requires
            self.well_formed(),
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    /// Inserts the given value into the set. Returns true if the value was not previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::insert()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.insert) for implementation details.
    pub fn insert(&mut self, k: String) -> (result: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    /// Removes the given value from the set. Returns true if the value was previously in the set, false otherwise.
    ///
    /// See Rust's [`HashSet::remove()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.remove) for implementation details.
    pub fn remove(&mut self, k: &str) -> (result: bool)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        proof {
            self.m.lemma_view();
        }
        let ghost before = self@;
        let ghost old_m = self.m.m@;
        let result = self.m.m.remove(k);
        proof {
            self.m.lemma_view();
            if !result && before.contains(k@) {
                let stored = choose|stored: String| #[trigger]
                    old_m.contains(stored) && stored@ == k@;
                assert(k.eq_spec(<String as BorrowSpec<str>>::borrow_spec(&stored)));
            }
            assert_sets_equal!(self@, before.remove(k@), view => {
                if self@.contains(view) {
                    let stored = choose|stored: String| #[trigger]
                        self.m.m@.contains(stored) && stored@ == view;
                    assert(view != k@);
                }
                if before.contains(view) && view != k@ {
                    let stored = choose|stored: String| #[trigger]
                        old_m.contains(stored) && stored@ == view;
                    assert(self.m.m@.contains(stored));
                }
            });
        }
        result
    }

    /// Returns true if the set contains the given value.
    ///
    /// See Rust's [`HashSet::contains()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.contains) for implementation details.
    pub fn contains(&self, k: &str) -> (result: bool)
        requires
            self.well_formed(),
        ensures
            result == self@.contains(k@),
    {
        self.get(k).is_some()
    }

    /// Returns a reference to the value in the set that is equal to the given value. If the value is not present in the set, returns `None`.
    ///
    /// See Rust's [`HashSet::get()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.get) for implementation details.
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a String>)
        requires
            self.well_formed(),
        ensures
            match result {
                Some(v) => self@.contains(k@) && v@ == k@,
                None => !self@.contains(k@),
            },
    {
        proof {
            self.m.lemma_view();
        }
        let result = self.m.m.get(k);
        proof {
            match result {
                Some(stored) => {
                    assert(stored@ == k@);
                },
                None => {
                    if self@.contains(k@) {
                        let stored = choose|stored: String| #[trigger]
                            self.m.m@.contains(stored) && stored@ == k@;
                        assert(k.eq_spec(<String as BorrowSpec<str>>::borrow_spec(&stored)));
                    }
                },
            }
        }
        result
    }

    /// Clears all values from the set.
    ///
    /// See Rust's [`HashSet::clear()`](https://doc.rust-lang.org/std/collections/struct.HashSet.html#method.clear) for implementation details.
    pub fn clear(&mut self)
        requires
            old(self).well_formed(),
        ensures
            final(self).well_formed(),
            final(self)@ == Set::<Seq<char>>::empty(),
    {
        self.m.clear()
    }
}

} // verus!
