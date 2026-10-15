// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    option_add_general_frame(None, option_frag(Some(7int)), Some(7int), Some(9int));
}

fn main() {
}

} // verus!
