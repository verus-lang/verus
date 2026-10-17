// EXPECTED-ERROR: precondition not satisfied
use vstd::resource::tsm_helpers as helpers;
#[path = "../ownership_helpers.rs"]
mod demo;
use vstd::prelude::*;
use vstd::resource::tsm::*;
verus! {

proof fn rejected() {
    let tracked map = helpers::singleton_map(0int, true);
    let tracked _value = helpers::take_singleton(map, 1int);
}

fn main() {
}

} // verus!
