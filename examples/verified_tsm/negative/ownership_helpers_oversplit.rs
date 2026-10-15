// EXPECTED-ERROR: precondition not satisfied
use vstd::resource::tsm_helpers as helpers;
#[path = "../ownership_helpers.rs"]
mod demo;
use vstd::prelude::*;
use vstd::resource::tsm::*;
verus! {

proof fn rejected() {
    let tracked owned = Token::<demo::Counts>::alloc_state(2);
    let tracked _parts = helpers::split_off(owned, CountRA { count: 3 });
}

fn main() {
}

} // verus!
