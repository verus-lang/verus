use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub trait Payload {
    spec fn score(self) -> int;
}

verified_tokenized_state_machine! {  Generic<T:Payload> {
    fields {
        #[sharding(constant)] pub limit:int,
        #[sharding(variable)] pub value:T,
        #[sharding(variable)] pub other:T,
    }
    #[invariant] pub fn inv(&self)->bool { self.value.score()<=self.limit && self.other.score()<=self.limit }
    init! { initialize(value:T,other:T,limit:int) {
        require value.score()<=limit;
        require other.score()<=limit;
        init limit=limit;
        init value=value;
        init other=other;
    } }
    transition! { set(value:T,__tsm_field_argument_value_0:nat,__tsm_field_reference_value_0:nat,__tsm_field_context_0:nat) {
        require value.score()<=pre.limit;
        require __tsm_field_argument_value_0==__tsm_field_reference_value_0;
        require __tsm_field_context_0==2;
        update other=pre.value;
        update value=value;
        assert pre.other.score()<=pre.limit;
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,value:T,other:T,limit:int) {}
    #[inductive(set)] fn set_inductive(pre:Self,post:Self,value:T,__tsm_field_argument_value_0:nat,__tsm_field_reference_value_0:nat,__tsm_field_context_0:nat) {}
}}

pub struct Number {
    pub x: int,
}

impl Payload for Number {
    open spec fn score(self) -> int {
        self.x
    }
}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut value), Tracked(mut other)) =
            Generic::Instance::initialize(Number { x: 3 }, Number { x: 4 }, 10);
        let tracked constant = instance.clone();
        instance.set(Number { x: 7 }, 8, 8, 2, &mut value, &mut other);
        assert(value.value().x == 7);
        assert(other.value().x == 3);
        assert(constant.limit() == 10);
    }
}

} // verus!
