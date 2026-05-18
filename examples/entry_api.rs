use vstd::prelude::*;
use vstd::std_specs::hash::*;
use std::hash::*;
use std::collections::hash_map::*;

verus!{

fn main() {
    let mut m = HashMap::<u64, u64>::new();

    // Use the entry to insert 0 => 20
    let entry0 = m.entry(0);
    entry0.insert_entry(20);

    // Use the entry to insert 1 => 30, then change it to 40
    let entry1 = m.entry(1);
    let mut occupied_entry = entry1.insert_entry(30);
    let value_ref = occupied_entry.get_mut();
    *value_ref = 40;

    assert(m@ =~= map![0 => 20, 1 => 40]);
}

/// Inserts the given key, value pair into the map if absent,
/// does nothing otherwise
fn insert_if_absent(m: &mut HashMap<u64, u64>, key: u64, value: u64)
    ensures
        !old(m)@.dom().contains(key) ==> final(m)@ =~= old(m)@.insert(key, value),
        old(m)@.dom().contains(key) ==> final(m)@ =~= old(m)@,
{
    m.entry(key).or_insert(value);
}

/// If the key is absent, insert 1; else, double it
fn try_double(m: &mut HashMap<u64, u64>, key: u64)
    requires
        m@.dom().contains(key) ==> m[key] * 2 <= u64::MAX,
    ensures
        !old(m)@.dom().contains(key) ==> final(m)@ =~= old(m)@.insert(key, 1),
        old(m)@.dom().contains(key) ==> final(m)@ =~= old(m)@.insert(key, (old(m)@[key] * 2) as u64)
{
    match m.entry(key) {
        Entry::Occupied(mut occ_entry) => {
            *occ_entry.get_mut() *= 2;
        }
        Entry::Vacant(vac_entry) => {
            vac_entry.insert(1);
        }
    }
}

}
