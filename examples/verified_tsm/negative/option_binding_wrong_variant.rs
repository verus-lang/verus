// EXPECTED-ERROR: precondition not satisfied
#[path = "../option_bindings.rs"]
mod definition;
use definition::{BoundOption, Payload};
use vstd::prelude::*;
verus! {

pub proof fn cannot_observe_a_different_variant() {
    let tracked all = BoundOption::Protocol::initialize(Payload::Empty);
    let tracked invalid = BoundOption::Protocol::observe(all);
}

} // verus!
fn main() {}
