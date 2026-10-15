// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    option_remove_general_frame(option_frag(Some(7int)), None, Some(7int), Some(9int));
}

fn main() {
}

} // verus!
