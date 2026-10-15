// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Replacement {
        fields {
            #[sharding(variable)] pub marker:nat,
            #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
        }
        init! {initialize(){init marker=0;init stored=IMap::empty();}}
        transition! {replace(){
            deposit stored +=[0nat=>43nat];
            withdraw stored -=[0nat=>43nat];
        }}
    }
}

} // verus!
fn main() {}
