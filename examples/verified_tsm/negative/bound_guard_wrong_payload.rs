// EXPECTED-ERROR: assertion failed
//! A logical binding cannot justify guarding a different stored value.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 WrongBoundGuard {
    fields {
        #[sharding(map)] pub observed:Map<int,u64>,
        #[sharding(storage_map)] pub stored:Map<int,u64>,
    }
    init! { initialize() {
        init observed=Map::empty().insert(1int,5u64);
        init stored=Map::empty().insert(1int,6u64);
    } }
    #[invariant] pub fn same_keys(self)->bool {
        self.observed.dom()==self.stored.dom()
    }
    #[invariant] pub fn stored_six(self)->bool {
        forall|key:int|self.stored.dom().contains(key) ==> self.stored[key]==6u64
    }
    property! { wrong_guard(key:int) {
        have observed >= [key=>let value];
        guard stored >= [key=>value];
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self){}
} }

} // verus!
fn main() {}
