// EXPECTED-ERROR: local-ready cannot observe a hidden or special-bound require
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(change)]
    Bound {
        fields {
            #[sharding(variable)] pub flag: bool,
            #[sharding(option)] pub logical: Option<nat>,
            #[sharding(storage_option)] pub storage: Option<nat>,
        }
        init! { initialize() {init flag=false;init logical=Some(7nat);init storage=None;} }
        transition! { change() {
            have logical>=Some(let value);
            require value==7;
            update flag=true;
        } }
    }
}

} // verus!
fn main() {}
