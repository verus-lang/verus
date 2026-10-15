// EXPECTED-ERROR: preconditions of an exchange cannot depend on such bindings
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    HiddenRequirement {
        fields {
            #[sharding(variable)] pub marker:nat,
            #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
        }
        init! {initialize(){init marker=0;init stored=IMap::empty();}}
        transition! {bad(){
            birds_eye let hidden=pre.stored;
            require hidden.dom().contains(0nat);
            update marker=1;
        }}
    }
}

} // verus!
fn main() {}
