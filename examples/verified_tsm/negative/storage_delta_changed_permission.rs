// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_storage::storage_delta;

verus! {

proof fn cannot_replace_a_retained_permission() {
    let old = IMap::<int, bool>::empty().insert(1, false);
    let new = IMap::<int, bool>::empty().insert(1, true);
    storage_delta(old, new);
}

fn main() {
}

} // verus!
