// EXPECTED-ERROR: precondition not satisfied
#[path = "../counting_to_n_atomic.rs"]
mod tutorial;
use tutorial::X;
use vstd::prelude::*;

verus! {

fn main() {
    proof {
        let tracked (
            Tracked(instance),
            Tracked(mut counter),
            Tracked(mut unstamped_tickets),
            Tracked(mut stamped_tickets),
        ) = X::Instance::initialize(2);
        instance.tr_inc(&mut counter, &mut unstamped_tickets, &mut stamped_tickets);
        instance.tr_inc(&mut counter, &mut unstamped_tickets, &mut stamped_tickets);
        instance.tr_inc(&mut counter, &mut unstamped_tickets, &mut stamped_tickets);
    }
}

} // verus!
