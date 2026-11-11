// EXPECTED-ERROR: a guard value must be a deterministic function of the local inputs
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    HiddenGuard {
        fields {
            #[sharding(variable)] pub marker:nat,
            #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
        }
        init! {initialize(){init marker=0;init stored=IMap::empty();}}
        property! {bad(){
            birds_eye let hidden=pre.stored[0nat];
            guard stored >=[0nat=>hidden];
        }}
    }
}

} // verus!
fn main() {}
