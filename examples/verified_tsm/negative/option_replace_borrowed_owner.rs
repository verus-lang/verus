// EXPECTED-ERROR: precondition not satisfied
//! FAIL: a compatible value in the frame does not provide local ownership.
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;

verus! {

proof fn replace_from_frame() {
    option_replace_frame(None, option_frag(Some(3nat)), Some(3nat), 3nat, 4nat);
}

fn main() {
}

} // verus!
