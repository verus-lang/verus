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

#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
pub struct HashSetWithView<Key> where Key: View + Eq + Hash {
    m: HashSet<Key>,
}

impl<Key> View for HashSetWithView<Key> where Key: View + Eq + Hash {
    type V = Set<<Key as View>::V>;

    closed spec fn view(&self) -> Self::V;
}

impl<Key> HashSetWithView<Key> where Key: View + Eq + Hash {
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

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    pub open spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: Key) -> (result: bool)
        ensures
            self@ == old(self)@.insert(k@) && result == !old(self)@.contains(k@),
    {
        self.m.insert(k)
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (result: bool)
        ensures
            self@ == old(self)@.remove(k@) && result == old(self)@.contains(k@),
    {
        self.m.remove(k)
    }

    #[verifier::external_body]
    pub fn contains(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains(k@),
    {
        self.m.contains(k)
    }

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

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Set::<<Key as View>::V>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast proof fn axiom_hash_set_with_view_spec_len<Key>(m: &HashSetWithView<Key>) where
    Key: View + Eq + Hash,

    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

#[verifier::ext_equal]
pub struct StringHashSet {
    m: HashSet<String>,
}

impl View for StringHashSet {
    type V = Set<Seq<char>>;

    closed spec fn view(&self) -> Self::V;
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

    pub open spec fn spec_len(&self) -> usize;

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

pub broadcast proof fn axiom_string_hash_set_spec_len(m: &StringHashSet)
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

pub broadcast group group_hash_set_axioms {
    axiom_hash_set_with_view_spec_len,
    axiom_string_hash_set_spec_len,
}

} // verus!
