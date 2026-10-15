// EXPECTED-ERROR: E0308
#[path = "../leader_election_complete.rs"]
mod original;
use original::*;
use vstd::prelude::*;
verus! {

fn main() {
    let tracked (Tracked(instance), Tracked(mut ids), Tracked(mut highest_heard)) =
        X::Instance::ini(seq![1int, 2int]);
    proof {
        instance.transmission(0, &mut highest_heard, &mut ids);
    }
}

} // verus!
