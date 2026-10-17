// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    option_remove_frame(None, option_frag(Some(4int)), Some(4int), 4int);
}

} // verus!
fn main() {}
