// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
#[path = "../counting_to_n.rs"]
mod demo;
verus! {

proof fn oversize_current_owner() {
    let tracked all = demo::X::Protocol::initialize(4);
    let tracked (local, other_owner) = demo::X::Protocol::split_unstamped_tickets(all, 2);
    let tracked _too_many = demo::X::Protocol::split_unstamped_tickets(local, 3);
}

} // verus!
fn main() {}
