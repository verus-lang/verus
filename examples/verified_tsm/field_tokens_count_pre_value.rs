use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {

    Produced {
        fields {
            #[sharding(variable)] pub counter:int,
            #[sharding(count)] pub c:nat,
        }
        init!{initialize(){init counter=3;init c=0;}}
        transition!{step(){add c += (pre.counter as nat);update counter=pre.counter+1;}}
    }
}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut counter), Tracked(empty)) =
            Produced::Instance::initialize();
        let tracked output = instance.step(&mut counter);
        assert(output.count() == 3);
        assert(counter.value() == 4);
        assert(output.instance_id() == instance.id());
    }
}

} // verus!
