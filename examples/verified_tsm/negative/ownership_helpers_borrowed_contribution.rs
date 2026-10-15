// EXPECTED-ERROR: precondition not satisfied
use vstd::resource::tsm_helpers as helpers;
#[path = "../ownership_helpers.rs"]
mod demo;
use vstd::prelude::*;
use vstd::resource::tsm::*;
verus! {

proof fn rejected() {
    let tracked all = Token::<demo::Counts>::alloc_state(9);
    let tracked (mut owned, shared) = all.split(CountRA { count: 2 }, CountRA { count: 7 });
    owned.validate_2(&shared);
    let tracked _parts = helpers::split_off(owned, CountRA { count: 3 });
}

fn main() {
}

} // verus!
