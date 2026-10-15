use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X{
fields{#[sharding(map)]pub c:Map<int,int>,}
#[invariant]pub fn only(self)->bool{forall|key:int,other:int|#[trigger]self.c.contains_key(key) && #[trigger]self.c.contains_key(other) ==> key==other}
init!{initialize(){init c=Map::empty().insert(0,7);}}
#[inductive(initialize)]fn initialize_inductive(post:Self){}
transition!{replace(old_key:int,key:int,old:int,next_value:int){remove c -=[old_key=>old];add c +=[key=>next_value];}}
#[inductive(replace)]fn replace_inductive(pre:Self,post:Self,old_key:int,key:int,old:int,next_value:int){broadcast use vstd::map::group_map_lemmas;broadcast use vstd::set::group_set_lemmas;}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut map)) = X::Instance::initialize();
        let tracked entry = map.remove(0);
        let tracked entry = instance.replace(0, 4, 7, 9, entry);
        assert(entry.key() == 4 && entry.value() == 9);
        map.insert(entry);

    }
}

} // verus!
