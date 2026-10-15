// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    let owned = persistent_option_frag(Some(4int));
    persistent_option_idempotent(Some(4int));
    persistent_option_insert_frame(owned, owned, Some(4int), 5int);
}

} // verus!
fn main() {}
