#![feature(allocator_api)]

use vstd::prelude::*;
use vstd::std_specs::hash::*;

use core::borrow::Borrow;
use std::collections::hash_map::*;
use std::hash::*;
use std::alloc::Allocator;

// Examples of using the HashMap::entry function
// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry

verus!{

// Specs for OccupiedEntry, VacantEntry, and the Entry enum
// OccupiedEntry and VacantEntry are both opaque;
// Entry is just an enum wrapper around the other 2, so we leave it transparent.

#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExOccupiedEntry<'a, K: 'a, V: 'a, A: Allocator>(OccupiedEntry<'a, K, V, A>);

#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExVacantEntry<'a, K: 'a, V: 'a, A: Allocator>(VacantEntry<'a, K, V, A>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(A)]
pub struct ExEntry<'a, K: 'a, V: 'a, A: Allocator>(Entry<'a, K, V, A>);

/// Specification for an [`OccupiedEntry`].
/// Contains the current key and value in the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
/// The final value is optional, since the user might choose to remove the entry.
pub trait OccupiedEntrySpecFns<K, V, A> : Sized {
    spec fn spec_key(self) -> K;
    spec fn value(self) -> V;
    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> OccupiedEntrySpecFns<K, V, A> for OccupiedEntry<'a, K, V, A> {
    uninterp spec fn spec_key(self) -> K;
    uninterp spec fn value(self) -> V;
    #[verifier::prophetic]
    uninterp spec fn final_value(self) -> Option<V>;
}

/// Specification for a [`VacantEntry`].
/// Contains the current key for the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
/// The final value is optional, since the user may or may not choose to insert a value.
pub trait VacantEntrySpecFns<K, V, A> : Sized {
    spec fn spec_key(self) -> K;
    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> VacantEntrySpecFns<K, V, A> for VacantEntry<'a, K, V, A> {
    uninterp spec fn spec_key(self) -> K;
    #[verifier::prophetic]
    uninterp spec fn final_value(self) -> Option<V>;
}

/// Specification for an [`Entry`].
/// Contains the current key for the entry,
/// and prophesies the final value after this instantiation of the entry API is complete.
pub trait EntrySpecFns<K, V, A> : Sized {
    spec fn spec_key(self) -> K;
    spec fn value(self) -> Option<V>;

    #[verifier::prophetic]
    spec fn final_value(self) -> Option<V>;
}

impl<'a, K, V, A: Allocator> EntrySpecFns<K, V, A> for Entry<'a, K, V, A> {
    open spec fn spec_key(self) -> K {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.spec_key(),
            Entry::Vacant(vacant_entry) => vacant_entry.spec_key(),
        }
    }

    open spec fn value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => Some(occupied_entry.value()),
            Entry::Vacant(vacant_entry) => None,
        }
    }

    #[verifier::prophetic]
    open spec fn final_value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.final_value(),
            Entry::Vacant(vacant_entry) => vacant_entry.final_value(),
        }
    }
}

pub broadcast axiom fn occupied_entry_has_resolved<K, V>(entry: OccupiedEntry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == Some(entry.value());

pub broadcast axiom fn vacant_entry_has_resolved<K, V>(entry: VacantEntry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == None::<V>;

pub broadcast proof fn entry_has_resolved<K, V>(entry: Entry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.final_value() == entry.value()
{
    broadcast use occupied_entry_has_resolved;
    broadcast use vacant_entry_has_resolved;
}

pub assume_specification<'a, Key: Hash + Eq, Value, S: BuildHasher, A: Allocator>
    [ HashMap::<Key, Value, S, A>::entry ]
    (m: &'a mut HashMap<Key, Value, S, A>, key: Key)
  -> (entry: Entry<'a, Key, Value, A>)
ensures
    obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> (
            entry.key() == key
         && entry.value() == old(m)@.get(key)
         && final(m)@ == (match entry.final_value() {
            Some(value) => old(m)@.insert(key, value),
            None => old(m)@.remove(key),
         })
    );

//// Entry

#[verifier::allow_in_spec]
pub assume_specification<'a, 'b, K, V, A: Allocator> [ Entry::key ]
    (entry: &'b Entry::<'a, K, V, A>) -> (key: &'b K)
returns
    &entry.spec_key();

pub assume_specification<'a, K, V, A: Allocator> [ Entry::or_insert ]
    (entry: Entry::<'a, K, V, A>, default: V) -> (value: &'a mut V)
ensures
    *value == (match entry.value() {
        Some(v) => v,
        None => default
    }),
    entry.final_value() == Some(*final(value));

pub assume_specification<'a, K, V, A: Allocator> [ Entry::insert_entry ]
    (entry: Entry::<'a, K, V, A>, value: V) -> (occ_entry: OccupiedEntry<'a, K, V, A>)
ensures
    occ_entry.key() == entry.key(),
    occ_entry.value() == value,
    entry.final_value() == occ_entry.final_value();

//// OccupiedEntry

// This module works around a bug with `allow_in_spec` that creates duplicate spec fn names
mod m_occ {
    use super::*;
    #[verifier::allow_in_spec]
    pub assume_specification<'a, 'b, K, V, A: Allocator> [ OccupiedEntry::key ]
        (entry: &'b OccupiedEntry::<'a, K, V, A>) -> (key: &'b K)
    returns
        &entry.spec_key();
}

pub assume_specification<'a, K, V, A: Allocator> [ OccupiedEntry::remove_entry ]
    (entry: OccupiedEntry::<'a, K, V, A>) -> (kv: (K, V))
ensures
    entry.final_value() === None,
returns
    (*entry.key(), entry.value());

pub assume_specification<'a, 'b, K, V, A: Allocator> [ OccupiedEntry::get ]
    (entry: &'b OccupiedEntry::<'a, K, V, A>) -> (value: &'b V)
ensures
    *value == entry.value();

pub assume_specification<'a, 'b, K, V, A: Allocator> [ OccupiedEntry::get_mut ]
    (entry: &'b mut OccupiedEntry::<'a, K, V, A>) -> (value: &'b mut V)
ensures
    *value == old(entry).value(),
    final(entry).key() == old(entry).key(),
    final(entry).value() == *final(value),
    final(entry).final_value() == old(entry).final_value();

pub assume_specification<'a, K, V, A: Allocator> [ OccupiedEntry::into_mut ]
    (entry: OccupiedEntry::<'a, K, V, A>) -> (value: &mut V)
ensures
    *value === entry.value(),
    entry.final_value() == Some(*final(value));

pub assume_specification<'a, K, V, A: Allocator> [ OccupiedEntry::insert ]
    (entry: &mut OccupiedEntry::<'a, K, V, A>, value: V) -> (old_value: V)
ensures
    old_value == old(entry).value(),
    final(entry).key() == old(entry).key(),
    final(entry).value() == value,
    final(entry).final_value() == old(entry).final_value();

pub assume_specification<'a, K, V, A: Allocator> [ OccupiedEntry::remove ]
    (entry: OccupiedEntry::<'a, K, V, A>) -> (value: V)
ensures
    value == entry.value(),
    entry.final_value() === None;

//// VacantEntry

// This module works around a bug with `allow_in_spec` that creates duplicate spec fn names
mod m_vac {
    use super::*;
    #[verifier::allow_in_spec]
    pub assume_specification<'a, 'b, K: 'a, V: 'a, A: Allocator> [ VacantEntry::key ]
        (entry: &'b VacantEntry::<'a, K, V, A>) -> (key: &'b K)
    returns
        &entry.spec_key();
}

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator> [ VacantEntry::into_key ]
    (entry: VacantEntry::<'a, K, V, A>) -> (key: K)
ensures
    key == entry.key(),
    entry.final_value() === None;

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator> [ VacantEntry::insert ]
    (entry: VacantEntry::<'a, K, V, A>, value: V) -> (value_ref: &mut V)
ensures
    *value_ref == value,
    entry.final_value() == Some(*final(value_ref));

pub assume_specification<'a, K: 'a, V: 'a, A: Allocator> [ VacantEntry::insert_entry ]
    (entry: VacantEntry::<'a, K, V, A>, value: V) -> (occ_entry: OccupiedEntry::<'a, K, V, A>)
ensures
    occ_entry.key() == entry.key(),
    occ_entry.value() == value,
    entry.final_value() == occ_entry.final_value();

fn main() {
    broadcast use entry_has_resolved;

    let mut m = HashMap::<u64, u64>::new();

    // Use entry API to insert to the map

    let entry = m.entry(5);
    assert(entry.key() == 5 && entry.value() === None);

    let value_ref = entry.or_insert(20);
    assert(*value_ref == 20);

    *value_ref = 40;

    assert(m@.dom().contains(5) && m@[5] == 40);

    // Use entry API to remove from the map

    let entry = m.entry(5);
    match entry {
        Entry::Occupied(occupied_entry) => {
            let (k, v) = occupied_entry.remove_entry();
            assert(k == 5);
            assert(v == 40);
        }
        Entry::Vacant(_) => {
            assert(false);
        }
    }

    assert(!m@.dom().contains(5));
}

fn test_occupied_entry() {
    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);
    let mut occ_entry = entry.insert_entry(20);

    assert(occ_entry.key() == 5);
    assert(occ_entry.value() == 20);

    let x = occ_entry.get();
    assert(*x == 20);

    let x = occ_entry.get_mut();
    assert(*x == 20);
    *x = 30;

    assert(occ_entry.key() == 5);
    assert(occ_entry.value() == 30);

    let x = occ_entry.into_mut();
    assert(*x == 30);
    *x = 40;

    assert(m@.dom().contains(5));
    assert(m@[5] == 40);

    // Now let's remove it

    let entry = m.entry(5);
    let mut occ_entry = entry.insert_entry(60);

    let (removed_key, removed_value) = occ_entry.remove_entry();
    assert(removed_key == 5);
    assert(removed_value == 60);

    assert(m@ =~= Map::empty());
}

fn test_occupied_entry2() {
    broadcast use occupied_entry_has_resolved;

    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);
    let mut occ_entry = entry.insert_entry(20);

    let old_value = occ_entry.insert(17);
    assert(old_value == 20);

    assert(m@.dom().contains(5));
    assert(m@[5] == 17);

    let entry = m.entry(5);
    let mut occ_entry = entry.insert_entry(20);
    let mut old_value = occ_entry.remove();
    assert(old_value == 20);

    assert(m@ =~= Map::empty());
}

fn test_vacant_entry() {
    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);

    let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

    let k = vac_entry.into_key();
    assert(k == 5);

    assert(m@ =~= Map::empty());
}

fn test_vacant_entry2() {
    broadcast use vacant_entry_has_resolved;

    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);

    let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

    // do nothing

    assert(m@ =~= Map::empty());
}

fn test_vacant_entry3() {
    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);

    let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

    let r = vac_entry.insert(20);
    assert(*r == 20);
    *r = 30;

    assert(m@.dom().contains(5) && m[5] == 30);
}

fn test_vacant_entry4() {
    broadcast use occupied_entry_has_resolved;
    let mut m = HashMap::<u64, u64>::new();
    let entry = m.entry(5);

    let Entry::Vacant(vac_entry) = entry else { assert(false); return; };

    let mut occ_entry = vac_entry.insert_entry(20);
    let r = occ_entry.get_mut();
    assert(*r == 20);
    *r = 30;

    assert(m@.dom().contains(5) && m[5] == 30);
}




}

