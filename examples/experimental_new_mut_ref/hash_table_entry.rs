use vstd::prelude::*;
use vstd::std_specs::hash::*;

use core::borrow::Borrow;
use std::collections::hash_map::*;
use std::hash::*;

// Examples of using the HashMap::entry function
// https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.entry

verus!{

// Specs for OccupiedEntry, VacantEntry, and the Entry enum

#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::reject_recursive_types_in_ground_variants(V)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExOccupiedEntry<'a, K: 'a, V: 'a>(OccupiedEntry<'a, K, V>);

#[verifier::reject_recursive_types_in_ground_variants(K)]
#[verifier::accept_recursive_types(V)]
#[verifier::external_body]
#[verifier::external_type_specification]
pub struct ExVacantEntry<'a, K: 'a, V: 'a>(VacantEntry<'a, K, V>);

#[verifier::external_type_specification]
pub struct ExEntry<'a, K: 'a, V: 'a>(Entry<'a, K, V>);

pub trait OccupiedEntrySpecFns<K, V> : Sized {
    spec fn key(self) -> K;
    spec fn value(self) -> V;
    #[verifier::prophetic]
    spec fn future_value(self) -> Option<V>;
}

impl<'a, K, V> OccupiedEntrySpecFns<K, V> for OccupiedEntry<'a, K, V> {
    uninterp spec fn key(self) -> K;
    uninterp spec fn value(self) -> V;
    #[verifier::prophetic]
    uninterp spec fn future_value(self) -> Option<V>;
}

pub trait VacantEntrySpecFns<K, V> : Sized {
    spec fn key(self) -> K;
    #[verifier::prophetic]
    spec fn future_value(self) -> Option<V>;
}

impl<'a, K, V> VacantEntrySpecFns<K, V> for VacantEntry<'a, K, V> {
    uninterp spec fn key(self) -> K;
    #[verifier::prophetic]
    uninterp spec fn future_value(self) -> Option<V>;
}

pub trait EntrySpecFns<K, V> : Sized {
    spec fn key(self) -> K;
    spec fn value(self) -> Option<V>;

    #[verifier::prophetic]
    spec fn future_value(self) -> Option<V>;
}

impl<'a, K, V> EntrySpecFns<K, V> for Entry<'a, K, V> {
    open spec fn key(self) -> K {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.key(),
            Entry::Vacant(vacant_entry) => vacant_entry.key(),
        }
    }

    open spec fn value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => Some(occupied_entry.value()),
            Entry::Vacant(vacant_entry) => None,
        }
    }

    #[verifier::prophetic]
    open spec fn future_value(self) -> Option<V> {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.future_value(),
            Entry::Vacant(vacant_entry) => vacant_entry.future_value(),
        }
    }
}

pub broadcast axiom fn occupied_entry_has_resolved<K, V>(entry: OccupiedEntry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.future_value() == Some(entry.value());

pub broadcast axiom fn vacant_entry_has_resolved<K, V>(entry: VacantEntry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.future_value() == None::<V>;

pub broadcast proof fn entry_has_resolved<K, V>(entry: Entry<K, V>)
    ensures
        #[trigger] has_resolved(entry) ==> entry.future_value() == entry.value()
{
    broadcast use occupied_entry_has_resolved;
    broadcast use vacant_entry_has_resolved;
}

pub assume_specification<
    'a,
    Key: Hash + Eq,
    Value,
    S: BuildHasher,
>[ HashMap::<Key, Value, S>::entry ](m: &'a mut HashMap<Key, Value, S>, key: Key)
  -> (entry: Entry<'a, Key, Value>)
ensures
    obeys_key_model::<Key>() && builds_valid_hashers::<S>() ==> (
            entry.key() == key
         && entry.value() == mut_ref_current(m)@.get(key)
         && mut_ref_future(m)@ == (match entry.future_value() {
            Some(value) => mut_ref_current(m)@.insert(key, value),
            None => mut_ref_current(m)@.remove(key),
         })
    );

pub assume_specification<'a, K, V> [ Entry::or_insert ]
    (entry: Entry::<'a, K, V>, default: V) -> (value: &'a mut V)
ensures
    mut_ref_current(value) == (match entry.value() {
        Some(v) => v,
        None => default
    }),
    entry.future_value() == Some(mut_ref_future(value));

pub assume_specification<'a, K, V> [ OccupiedEntry::remove_entry ]
    (entry: OccupiedEntry::<'a, K, V>) -> (kv: (Key, Value))
ensures
    entry.future_value() == None,
returns
    (entry.key(), entry.value())


fn main() {
    broadcast use entry_has_resolved;

    let mut m = HashMap::<u64, u64>::new();

    // Use entry API to insert to the matp

    let entry = m.entry(5);
    assert(entry.key() == 5 && entry.value() === None);

    let value_ref = entry.or_insert(20);
    assert(*value_ref == 20);

    *value_ref = 40;

    assert(m@.dom().contains(5) && m@[5] == 40);

    // Use entry API to remove from the map

    let entry = m.entry(5);
    match entry {
        Entry::OccupiedEntry(occupied_entry) => {
            let (k, v) == occupied_entry.remove_entry();
            assert(k == 5);
            assert(v == 40);
        }
        Entry::VacantEntry(_) => {
            assert(false);
        }
    }

    assert(!m@.dom().contains(5));
}

}

