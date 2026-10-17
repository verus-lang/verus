// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_context::Descriptor;

verus! {

proof fn different_descriptors_do_not_imply_equal_metadata() {
    let tracked left = Descriptor::alloc(7int);
    let tracked right = Descriptor::alloc(9int);
    left.agrees(&right);
}

} // verus!
fn main() {}
