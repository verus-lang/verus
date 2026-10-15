// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_bool::*;

verus! {

proof fn local_absence_does_not_allow_addition() {
    // The caller's fragment is empty, but the frame owns the present boolean.
    bool_add_frame(bool_frag(false), bool_frag(true), true);
}

fn main() {
}

} // verus!
