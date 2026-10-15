// EXPECTED-ERROR: precondition not satisfied
#[path = "../leader_election_complete.rs"]
mod original;
use original::*;
use vstd::prelude::*;
verus! {

fn main() {
    let tracked (Tracked(instance), Tracked(ids), Tracked(highest_heard)) = X::Instance::ini(
        seq![1int, 1int],
    );
}

} // verus!
