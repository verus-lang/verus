// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    let full = IMap::empty().insert(0int, 4int);
    let owned = persistent_map_frag(full);
    let frame = persistent_map_frag(full);
    persistent_map_idempotent(full);
    persistent_map_insert_frame(owned, frame, full, 0int, 5int);
}

} // verus!
fn main() {}
