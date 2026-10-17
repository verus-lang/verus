// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {

    Bound {
        fields {
            #[sharding(constant)] pub limit:int,
            #[sharding(variable)] pub counter:int,
        }
        #[invariant] pub fn bounded(&self)->bool {self.counter<=self.limit}
        init!{initialize(limit:int){require limit>=0;init limit=limit;init counter=0;}}
        transition!{set(n:int){require n<=pre.limit;assert(pre.counter<=pre.limit);update counter=n;}}
        property!{check(){assert(pre.counter<=pre.limit);}}
        #[inductive(initialize)] fn initialize_inductive(post:Self,limit:int){}
        #[inductive(set)] fn set_inductive(pre:Self,post:Self,n:int){}
    }
}

fn main() {
    proof {
        let tracked token = Bound::Instance::initialize(-1);
    }
}

} // verus!
