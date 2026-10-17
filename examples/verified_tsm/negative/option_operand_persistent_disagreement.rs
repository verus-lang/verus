// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    persistent_option_union_general_frame(
        None,
        persistent_option_frag(Some(7int)),
        Some(7int),
        Some(9int),
    );
}

fn main() {
}

} // verus!
