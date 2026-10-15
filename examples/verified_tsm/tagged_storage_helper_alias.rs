use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
type __StorageKey = nat;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
Mixed<T> {
    fields {
        #[sharding(variable)] pub phase:nat,
        #[sharding(not_tokenized)] pub payload:T,
        #[sharding(storage_option)] pub first:Option<u64>,
        #[sharding(storage_map)] pub second:Map<nat,bool>,
    }
    pub open spec fn original_helper(&self)->__StorageKey {0nat}
    init! {initialize(payload:T) {
        init phase=0;init payload=payload;init first=None;init second=Map::empty();
    }}
    transition! {deposit_all(value:u64,values:Map<nat,bool>) {
        require pre.phase==0;
        require values.dom()==Set::empty().insert(0nat);
        deposit first+=Some(value);
        deposit second+=(values);
        update phase=1;
    }}
    transition! {take_first() {
        require pre.phase==1;
        withdraw first-=Some(let value);
        update phase=2;
    }}
    transition! {take_second() {
        require pre.phase==2;
        withdraw second-=[0nat=>let value];
        update phase=3;
    }}
    #[invariant] pub fn stages(&self)->bool {
        &&& self.phase<=3
        &&& self.phase==0 ==> self.first is None && self.second==Map::empty()
        &&& self.phase==1 ==> self.first is Some && self.second.dom()==Set::empty().insert(0nat)
        &&& self.phase==2 ==> self.first is None && self.second.dom()==Set::empty().insert(0nat)
        &&& self.phase==3 ==> self.first is None && self.second==Map::empty()
    }
    #[inductive(initialize)] fn initialize_inductive(post:Self,payload:T) {}
    #[inductive(deposit_all)] fn deposit_all_inductive(pre:Self,post:Self,value:u64,values:Map<nat,bool>) {
        broadcast use vstd::map::group_map_lemmas;
        assert(post.second =~= values);
    }
    #[inductive(take_first)] fn take_first_inductive(pre:Self,post:Self) {}
    #[inductive(take_second)] fn take_second_inductive(pre:Self,post:Self) {
        broadcast use vstd::map::group_map_lemmas;
        assert(post.second =~= Map::empty());
    }
}}
verus! {

fn main() {
}

} // verus!
