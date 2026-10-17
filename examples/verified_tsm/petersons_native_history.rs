#[path = "petersons_algorithm.rs"]
mod protocol;
use protocol::{Petersons, ThreadState};
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

        instance.t0_set_flag(&mut flag_0, &mut thread_0);
        instance.t0_set_turn(&mut turn, &mut thread_0);
        let tracked permission = instance.t0_enter_via_flag(&mut thread_0, &flag_1);
        assert(thread_0.value() == ThreadState::Critical);
        instance.t0_done(permission, &mut flag_0, &mut thread_0, permission);

        instance.t1_set_flag(&mut flag_1, &mut thread_1);
        instance.t1_set_turn(&mut turn, &mut thread_1);
        let tracked permission = instance.t1_enter_via_flag(&mut thread_1, &flag_0);
        assert(thread_1.value() == ThreadState::Critical);
        instance.t1_done(permission, &mut flag_1, &mut thread_1, permission);

        instance.t0_set_flag(&mut flag_0, &mut thread_0);
        instance.t0_set_turn(&mut turn, &mut thread_0);
        instance.t1_set_flag(&mut flag_1, &mut thread_1);
        instance.t1_set_turn(&mut turn, &mut thread_1);
        let tracked permission = instance.t0_enter_via_turn(&mut thread_0, &turn);
        assert(thread_0.value() == ThreadState::Critical);
        assert(thread_1.value() == ThreadState::Waiting);
        instance.t0_done(permission, &mut flag_0, &mut thread_0, permission);

        instance.t0_set_flag(&mut flag_0, &mut thread_0);
        instance.t0_set_turn(&mut turn, &mut thread_0);
        let tracked permission = instance.t1_enter_via_turn(&mut thread_1, &turn);
        assert(thread_1.value() == ThreadState::Critical);
        assert(thread_0.value() == ThreadState::Waiting);
        instance.t1_done(permission, &mut flag_1, &mut thread_1, permission);
        let tracked permission = instance.t0_enter_via_flag(&mut thread_0, &flag_1);
        instance.t0_done(permission, &mut flag_0, &mut thread_0, permission);
        assert(!flag_0.value() && !flag_1.value());
        assert(thread_0.value() == ThreadState::Idle);
        assert(thread_1.value() == ThreadState::Idle);
    }
}

} // verus!
