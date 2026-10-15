// EXPECTED-ERROR: unowned fields cannot be read by a token operation
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {

    Consumed {
        fields {
            #[sharding(variable)] pub counter:int,
            #[sharding(count)] pub input:nat,
            #[sharding(count)] pub output:nat,
        }
        #[invariant] pub fn inv(&self)->bool {self.input+self.counter==1}
        init!{initialize(){init counter=0;init input=1;init output=0;}}
        transition!{step(){require(pre.counter==0);remove input -= (1);add output += (pre.input);update counter=pre.counter+1;}}
        #[inductive(initialize)] fn initialize_inductive(post:Self){}
        #[inductive(step)] fn step_inductive(pre:Self,post:Self){}
    }
}

proof fn test() {
    let tracked (Tracked(instance), Tracked(mut counter), Tracked(input), Tracked(empty)) =
        Consumed::Instance::initialize();
    let tracked output = instance.step(&mut counter, input);
    assert(output.count() == 1);
    assert(counter.value() == 1);
}

fn main() {
    proof {
        test();
    }
}

} // verus!
