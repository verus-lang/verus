//! Exact physical deposits and withdrawals derived from agreeing storage maps.
use vstd::prelude::*;
use vstd::resource::tsm_storage::{storage_delta, storage_partition};

verus! {

broadcast use vstd::imap::group_imap_lemmas;

proof fn deposit_and_withdraw() {
    let old = IMap::<int, bool>::empty().insert(1, true).insert(2, false);
    let new = IMap::<int, bool>::empty().insert(2, false).insert(3, true);
    assert(old.agrees(new));
    storage_delta(old, new);
    let deposit = new.remove_keys(old.dom());
    let combined = old.union_prefer_right(deposit);
    storage_partition(combined, new);
    let withdraw = combined.remove_keys(new.dom());
    assert(deposit =~= IMap::empty().insert(3, true));
    assert(withdraw =~= IMap::empty().insert(1, true));
    assert(old.dom().disjoint(deposit.dom()));
    assert(new.dom().disjoint(withdraw.dom()));
    assert(combined =~= new.union_prefer_right(withdraw));
}

proof fn retained_resources_are_unchanged() {
    let stored = IMap::<int, bool>::empty().insert(1, true);
    storage_delta(stored, stored);
    let deposit = stored.remove_keys(stored.dom());
    storage_partition(stored.union_prefer_right(deposit), stored);
    assert(deposit =~= IMap::empty());
    assert(stored.remove_keys(stored.dom()) =~= IMap::empty());
}

fn main() {
}

} // verus!
