// EXPECTED-ERROR: duplicate local-ready transition
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(change,change)]
    Names {
        fields {
            #[sharding(variable)] pub value: nat,
            #[sharding(storage_option)] pub storage: Option<nat>,
        }
        init! { initialize() {init value=0;init storage=None;} }
        transition! { change(observed:nat,initial:nat,physical_deposit:nat,next:nat,certificate:nat) {
            require observed==initial;
            update value=observed+physical_deposit+next+certificate;
        } }
    }
}

} // verus!
fn main() {}
