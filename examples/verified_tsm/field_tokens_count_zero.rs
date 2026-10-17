use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!( Sample {fields { #[sharding(count)] pub value:nat, } init!{initialize(){init value=0;}}});
verus! {

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(value)) = Sample::Instance::initialize();
        assert(value.count() == 0);
        assert(value.instance_id() == instance.id());
    }
}

} // verus!
