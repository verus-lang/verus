// EXPECTED-ERROR: assertion failed
//! The existing physical kernel requires deposits to be disjoint from OLD storage.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 OldKeyReplacement {
    fields {
        #[sharding(variable)] pub auth:IMap<nat,nat>,
        #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
    }
    #[invariant] pub fn same(&self)->bool {self.auth==self.stored}
    init! {initialize(){
        init auth=IMap::empty().insert(0nat,43nat);
        init stored=IMap::empty().insert(0nat,43nat);
    }}
    transition! {replace(){
        require(pre.auth==IMap::empty().insert(0nat,43nat));
        withdraw stored -= [0nat=>43nat];
        deposit stored += [0nat=>43nat];
        update auth=IMap::empty().insert(0nat,43nat);
    }}
    #[inductive(initialize)] fn initialize_inductive(post:Self){}
    #[inductive(replace)] fn replace_inductive(pre:Self,post:Self){
        assert(post.stored =~= post.auth);
    }
} }

} // verus!
fn main() {}
