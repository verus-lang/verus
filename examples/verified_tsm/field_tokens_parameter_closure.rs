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
            update value = if ISet::new(|__tsm_field_argument_value_0:int| __tsm_field_argument_value_0 == pre.value).contains(value) { value } else { value };
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self, limit:int) {}
        #[inductive(set)] fn set_inductive(pre:Self, post:Self, value:int) {}
    }
}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut value)) = Constant::Instance::initialize(10);
        let tracked constant = instance.clone();
        instance.set(9, &mut value);
        assert(constant.limit() == 10);
        assert(value.value() == 9);
        constant.set(4, &mut value);
        assert(value.value() == 4);
    }
}

} // verus!
