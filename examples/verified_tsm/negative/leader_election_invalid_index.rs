// EXPECTED-ERROR: precondition not satisfied
#[path = "../leader_election_complete.rs"]
mod original;
use original::*;
use vstd::prelude::*;
verus! {

fn main() {
    let tracked (Tracked(instance), Tracked(mut ids), Tracked(mut highest_heard)) =
        X::Instance::ini(seq![1int, 2int]);
    proof {
        instance.transmission(2, &mut ids, &mut highest_heard);
    }
}

} // verus!
