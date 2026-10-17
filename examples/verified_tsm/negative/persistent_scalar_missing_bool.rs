// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_persistent_scalars.rs"]
mod demo;
use demo::PersistentScalars;
use vstd::prelude::*;
verus! {

proof fn missing_true() {
    let tracked token = PersistentScalars::Protocol::initialize(None, false, 9nat);
    let tracked _out = PersistentScalars::Protocol::observe_optional(token, None, true, 0nat);
}

} // verus!
fn main() {}
