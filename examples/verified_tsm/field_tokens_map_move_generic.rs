use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X<#[verifier::reject_recursive_types] K,V>{
fields{#[sharding(imap)]pub c:IMap<K,V>,}
#[invariant]pub fn only(self)->bool{forall|key:K,other:K|#[trigger]self.c.contains_key(key) && #[trigger]self.c.contains_key(other) ==> key==other}
init!{initialize(key:K,value:V){init c=IMap::empty().insert(key,value);}}
#[inductive(initialize)]fn initialize_inductive(post:Self,key:K,value:V){}
transition!{replace(old_key:K,key:K,old:V,next_value:V){remove c -=[old_key=>old];add c +=[key=>next_value];}}
#[inductive(replace)]fn replace_inductive(pre:Self,post:Self,old_key:K,key:K,old:V,next_value:V){broadcast use vstd::imap::group_imap_lemmas;broadcast use vstd::iset::group_iset_lemmas;}
}}

pub proof fn demonstration<K, V>(key: K, next_key: K, value: V, next_value: V) {
    let tracked (Tracked(instance), Tracked(mut map)) = X::Instance::<K, V>::initialize(key, value);
    let tracked entry = map.remove(key);
    let tracked entry = instance.replace(key, next_key, value, next_value, entry);
    assert(entry.key() == next_key && entry.value() == next_value);
    map.insert(entry);
}

fn main() {
}

} // verus!
