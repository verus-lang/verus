// EXPECTED-ERROR: precondition not satisfied
#[path = "../ordered_ownership.rs"]
mod ordered;
use ordered::*;
use vstd::prelude::*;
verus! {

proof fn borrowed_count_does_not_authorize_removal() {
    let tracked (owner, shared) = allocate_shared(0nat, 3nat);
    let tracked token = Ordered::Protocol::remove_then_have_with_shared(owner, &shared);
}

fn main() {
}

} // verus!
