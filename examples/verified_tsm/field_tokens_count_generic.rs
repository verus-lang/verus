use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::thread::*;
verus! {

verified_tokenized_state_machine! {

    GenericCount<T> {
        fields {
            #[sharding(constant)] pub value:T,
            #[sharding(variable)] pub flag:bool,
            #[sharding(count)] pub input:nat,
            #[sharding(count)] pub output:nat,
        }
        #[invariant] pub fn inv(&self)->bool {self.input+self.output==1 && self.output==(if self.flag {1nat}else{0nat})}
        init!{initialize(value:T){init value=value;init flag=false;init input=1;init output=0;}}
        transition!{consume(){require(!pre.flag);remove input -= (1);add output += (1);update flag=true;}}
        property!{done(){have output >= (1);assert(pre.flag);}}
        #[inductive(initialize)] fn initialize_inductive(post:Self,value:T){}
        #[inductive(consume)] fn consume_inductive(pre:Self,post:Self){}
    }
}

fn main() {
    let tracked (Tracked(instance), Tracked(flag), Tracked(mut input), Tracked(output)) =
        GenericCount::Instance::<u64>::initialize(7);
    let tracked ticket = input.split(1);
    let tracked instance = instance.clone();
    let ghost id = instance.id();
    let handle = spawn(
        move || -> (result: Tracked<GenericCount::output<u64>>)
            ensures
                result@.instance_id() == id,
                result@.count() == 1,
            {
                let tracked mut flag = flag;
                let tracked result;
                proof {
                    result = instance.consume(&mut flag, ticket);
                    instance.done(&flag, &result);
                    assert(instance.value() == 7);
                }
                Tracked(result)
            },
    );
    match handle.join() {
        Ok(result) => {
            proof {
                assert(result@.count() == 1);
            }
        },
        Err(_) => {},
    }
}

} // verus!
