use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub trait Limit {
    spec fn maximum(self) -> int;
}

pub struct Bound {
    pub n: int,
}

impl Limit for Bound {
    open spec fn maximum(self) -> int {
        self.n
    }
}

verified_tokenized_state_machine! {  Bounded<L:Limit> {
    fields {
        #[sharding(constant)] pub limit:L,
        #[sharding(variable)] pub value:int,
    }
    #[invariant] pub fn inv(&self)->bool {self.value<=self.limit.maximum()}
    init! { initialize(limit:L) {
        require limit.maximum()>=0;
        init limit=limit;
        init value=0;
    } }
    transition! { set(value:int,b:bool) {
        if b {
            require value<=pre.limit.maximum();
            update value=value;
        } else {
            update value=pre.value-1;
        }
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,limit:L) {}
    #[inductive(set)] fn set_inductive(pre:Self,post:Self,value:int,b:bool) {}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut value)) = Bounded::Instance::initialize(
            Bound { n: 10 },
        );
        let tracked constant = instance.clone();
        instance.set(9, true, &mut value);
        assert(value.value() == 9);
        constant.set(30, false, &mut value);
        assert(value.value() == 8);
        assert(instance.limit().n == 10 && constant.limit().n == 10);
    }
}

} // verus!
