#[path = "leader_election_complete.rs"]
mod original;
use original::*;
use vstd::prelude::*;
verus! {

fn main() {
    let tracked (Tracked(instance), Tracked(mut ids), Tracked(mut highest_heard)) =
        X::Instance::ini(seq![1int, 2int]);
    proof {
        instance.transmission(0, &mut ids, &mut highest_heard);
        assert(highest_heard.value() == seq![-1int, 1int]);
        instance.transmission(1, &mut ids, &mut highest_heard);
        assert(highest_heard.value() == seq![2int, 1int]);
        instance.transmission(0, &mut ids, &mut highest_heard);
        assert(highest_heard.value() == seq![2int, 2int]);
        instance.transmission(1, &mut ids, &mut highest_heard);
        assert(highest_heard.value() == seq![2int, 2int]);
        assert(ids.value() == seq![1int, 2int]);
        let state = X::State { ids: ids.value(), highest_heard: highest_heard.value() };
        assert(state.is_leader(1));
        assert(!state.is_leader(0));
        assert(state.safety_condition());
    }
}

} // verus!
