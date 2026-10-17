// EXPECTED-ERROR: precondition not satisfied
//! Full-state count nine does not grant two remaining LOCAL count rights.
#[path = "../ordered_ownership.rs"]
mod ordered;
use ordered::*;
use vstd::prelude::*;
verus! {

proof fn spent_rights_cannot_be_observed_again() {
    let tracked token = Ordered::Protocol::remove_then_have(allocate_local(2nat));
}

fn main() {
}

} // verus!
