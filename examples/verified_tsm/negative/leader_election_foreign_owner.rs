// EXPECTED-ERROR: precondition not satisfied
#[path = "../leader_election_complete.rs"]
mod original;
use original::*;
use vstd::prelude::*;
verus! {

fn main() {
    let tracked (Tracked(instance), Tracked(mut ids), Tracked(mut highest_heard)) =
        X::Instance::ini(seq![1int, 2int]);
    let tracked (Tracked(other), Tracked(mut other_ids), Tracked(other_highest_heard)) =
        X::Instance::ini(seq![3int, 4int]);
    proof {
        instance.transmission(0, &mut other_ids, &mut highest_heard);
    }
}

} // verus!
