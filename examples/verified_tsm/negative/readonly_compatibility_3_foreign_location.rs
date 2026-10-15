// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm::*;
#[path = "../readonly_compatibility_3.rs"]
mod model;
verus! {

proof fn third_reference_must_have_the_same_location() {
    let tracked first = Token::<model::Boolean>::alloc_state(true);
    let tracked third = Token::<model::Boolean>::alloc_state(false);
    let state = first.compatible_3(&first, &third);
}

fn main() {
}

} // verus!
