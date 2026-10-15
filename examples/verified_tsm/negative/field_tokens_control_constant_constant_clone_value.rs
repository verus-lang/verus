// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  Bounded {
    fields {
        #[sharding(constant)] pub limit:int,
        #[sharding(variable)] pub value:int,
    }
    #[invariant] pub fn inv(&self)->bool {self.value<=self.limit}
    init! { initialize(limit:int) {
        require limit>=0;
        init limit=limit;
        init value=0;
    } }
    transition! { set(value:int,b:bool) {
        if b {
            require value<=pre.limit;
            update value=value;
        } else {
            update value=pre.value-1;
        }
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,limit:int) {}
    #[inductive(set)] fn set_inductive(pre:Self,post:Self,value:int,b:bool) {}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(_value)) = Bounded::Instance::initialize(10);
        let tracked constant = instance.clone();
        assert(constant.limit() == 20);
    }
}

} // verus!
