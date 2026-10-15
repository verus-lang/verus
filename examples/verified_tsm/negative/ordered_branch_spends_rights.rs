// EXPECTED-ERROR: precondition not satisfied
#[path = "../ordered_ownership.rs"]
mod ordered;
use ordered::*;
use vstd::prelude::*;
verus! {

proof fn selected_branch_changes_ownership() {
    let tracked token = Ordered::Protocol::branch_then_have(allocate_local(2nat), true);
}

fn main() {
}

} // verus!
