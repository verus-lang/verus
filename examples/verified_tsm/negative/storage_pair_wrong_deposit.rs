// EXPECTED-ERROR: precondition not satisfied
#[path = "../storage_pair_transfers.rs"]
mod fixture;
use fixture::*;
use vstd::cell::PCell;
use vstd::prelude::*;
verus! {

fn incorrect_physical_keys() {
    let (left, Tracked(old)) = PCell::new(7u64);
    let (right, Tracked(incoming)) = PCell::new(8u64);
    let ghost old_value = old;
    let ghost incoming_value = incoming;
    let tracked mut initial = IMap::tracked_empty();
    proof {
        initial.tracked_insert(0nat, old);
    }
    let tracked token = PhysicalPair::Protocol::initialize(initial, old_value);
    let tracked mut supplied = IMap::tracked_empty();
    proof {
        supplied.tracked_insert(2nat, incoming);
    }
    let tracked token = PhysicalPair::Protocol::swap(token, supplied, old_value, incoming_value);
}

fn main() {
}

} // verus!
