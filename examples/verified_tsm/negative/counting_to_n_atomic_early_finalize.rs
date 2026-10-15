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
        instance.finalize(&counter, &stamped_tickets);
    }
}

} // verus!
