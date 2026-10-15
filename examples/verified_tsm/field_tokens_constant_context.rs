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
        let tracked (Tracked(instance), Tracked(mut counter)) = Bound::Instance::initialize(10);
        let tracked clone = instance.clone();
        clone.set(9, &mut counter);
        clone.check(&counter);
        assert(counter.value() == 9);
        instance.set(3, &mut counter);
        instance.check(&counter);
        assert(counter.value() == 3);
        assert(clone.limit() == 10);
    }
}

} // verus!
