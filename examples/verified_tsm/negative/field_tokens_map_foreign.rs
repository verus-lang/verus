// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X{
fields{#[sharding(imap)]pub c:IMap<int,int>,}
#[invariant]pub fn only(self)->bool{forall|key:int,other:int|#[trigger]self.c.contains_key(key) && #[trigger]self.c.contains_key(other) ==> key==other}
init!{initialize(){init c=IMap::empty().insert(0,7);}}
#[inductive(initialize)]fn initialize_inductive(post:Self){}
transition!{replace(old_key:int,key:int,old:int,next_value:int){remove c -=[old_key=>old];add c +=[key=>next_value];}}
#[inductive(replace)]fn replace_inductive(pre:Self,post:Self,old_key:int,key:int,old:int,next_value:int){broadcast use vstd::imap::group_imap_lemmas;broadcast use vstd::iset::group_iset_lemmas;}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut map)) = X::Instance::initialize();
        let tracked entry = map.remove(0);
        let tracked (Tracked(other_instance), Tracked(mut other_map)) = X::Instance::initialize();
        let tracked other_entry = other_map.remove(0);
        let tracked entry = instance.replace(0, 4, 7, 9, other_entry);
        assert(entry.key() == 4 && entry.value() == 9);
        map.insert(entry);

    }
}

} // verus!
