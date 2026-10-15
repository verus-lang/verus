// EXPECTED-ERROR: precondition not satisfied
#[path = "../petersons_algorithm.rs"]
mod protocol;
use protocol::Petersons;
use vstd::prelude::*;

verus! {

fn main() {
    proof {
        let tracked permission = 7int;
        let tracked (
            Tracked(instance),
            Tracked(mut flag_0),
            Tracked(mut flag_1),
            Tracked(mut turn),
            Tracked(mut thread_0),
            Tracked(mut thread_1),
        ) = Petersons::Instance::initialize(permission, Some(permission));
        let tracked permission = instance.t0_enter_via_flag(&mut thread_0, &flag_1);
    }
}

} // verus!
