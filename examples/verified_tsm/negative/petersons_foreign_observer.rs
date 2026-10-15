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
        let tracked other_permission = 13int;
        let tracked (
            Tracked(other_instance),
            Tracked(other_flag_0),
            Tracked(other_flag_1),
            Tracked(other_turn),
            Tracked(other_thread_0),
            Tracked(other_thread_1),
        ) = Petersons::Instance::initialize(other_permission, Some(other_permission));
        instance.t0_set_flag(&mut flag_0, &mut thread_0);
        instance.t0_set_turn(&mut turn, &mut thread_0);
        let tracked permission = instance.t0_enter_via_flag(&mut thread_0, &other_flag_1);
    }
}

} // verus!
