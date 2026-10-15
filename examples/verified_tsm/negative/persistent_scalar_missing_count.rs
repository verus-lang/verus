// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_persistent_scalars.rs"]
mod demo;
use demo::PersistentScalars;
use vstd::prelude::*;
verus! {

proof fn missing_lower_bound() {
    let tracked token = PersistentScalars::Protocol::initialize(None, true, 9nat);
    let tracked _out = PersistentScalars::Protocol::observe_optional(token, None, false, 800nat);
}

} // verus!
fn main() {}
