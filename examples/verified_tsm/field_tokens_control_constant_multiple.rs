use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  Bounded {
    fields {
        #[sharding(constant)] pub limit:int,
        #[sharding(variable)] pub value:int,
        #[sharding(constant)] pub step:int,
        #[sharding(variable)] pub spare:int,
    }
    #[invariant] pub fn inv(&self)->bool {self.value<=self.limit && self.spare<=self.limit && self.step>0}
    init! { initialize(limit:int,step:int) {
        require limit>=0 && step>0;
        init limit=limit;
        init value=0;
        init step=step;
        init spare=0;
    } }
    transition! { set(value:int,b:bool) {
        if b {
            require value+pre.step<=pre.limit;
            update value=value;
            update spare=value+pre.step;
        } else {
            update value=pre.value-pre.step;
            update spare=pre.spare-pre.step;
        }
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,limit:int,step:int) {}
    #[inductive(set)] fn set_inductive(pre:Self,post:Self,value:int,b:bool) {}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut value), Tracked(mut spare)) =
            Bounded::Instance::initialize(10, 2);
        let tracked constant = instance.clone();
        instance.set(7, true, &mut value, &mut spare);
        assert(value.value() == 7 && spare.value() == 9);
        constant.set(30, false, &mut value, &mut spare);
        assert(value.value() == 5 && spare.value() == 7);
        assert(instance.limit() == 10 && constant.limit() == 10);
        assert(instance.step() == 2 && constant.step() == 2);
    }
}

} // verus!
