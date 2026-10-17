// EXPECTED-ERROR: precondition not satisfied
#[path = "../persistent_optional.rs"]
mod demo;
use vstd::prelude::*;
verus! {

proof fn a_persistent_observation_does_not_change_value() {
    let tracked token = demo::PersistentOptional::Protocol::initialize();
    let tracked token = demo::PersistentOptional::Protocol::record(token, Some(7int));
    let tracked output = demo::PersistentOptional::Protocol::observe(token, Some(8int));
}

} // verus!
fn main() {}
