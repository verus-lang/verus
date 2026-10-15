use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X{
fields{#[sharding(imap)]pub c:IMap<int,int>,}
init!{initialize(){init c=IMap::empty().insert(0,7).insert(1,9);}}
#[invariant]pub fn zero(self)->bool{self.c.contains_key(0) ==> self.c[0]==7}
property!{same(key:int,value:int){require key==0;have c >=[key=>value];assert value==7;}}
#[inductive(initialize)]fn initialize_inductive(post:Self){}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut map)) = X::Instance::initialize();
        let tracked entry = map.remove(0);
        instance.same(0, entry.value(), &entry);
        assert(entry.key() == 0 && entry.value() == 7);
        map.insert(entry);

    }
}

} // verus!
