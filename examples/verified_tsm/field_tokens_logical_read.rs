use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X{
fields{#[sharding(imap)]pub c:IMap<int,int>,}
init!{initialize(){init c=IMap::empty().insert(0,7).insert(1,9);}}
transition!{same(){have c >=[0=>7];}}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut map)) = X::Instance::initialize();
        let tracked entry = map.remove(0);
        instance.same(&entry);
        assert(entry.key() == 0 && entry.value() == 7);
        map.insert(entry);

    }
}

} // verus!
