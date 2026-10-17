// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
     Constant {
        fields {
            #[sharding(constant)] pub limit: int,
            #[sharding(variable)] pub value: int,
        }
        #[invariant] pub fn inv(&self) -> bool { self.value <= self.limit }
        init! { initialize(limit: int) {
            require limit >= 0;
            init limit = limit;
            init value = 0;
        } }
        transition! { set(value: int) {
            require value <= pre.limit;
            update value = value;
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self, limit:int) {}
        #[inductive(set)] fn set_inductive(pre:Self, post:Self, value:int) {}
    }
}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut value)) = Constant::Instance::initialize(10);
        instance.set(11, &mut value);
    }
}

} // verus!
