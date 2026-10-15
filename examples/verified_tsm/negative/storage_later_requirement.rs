// EXPECTED-ERROR: verified backend requires remove/have statements before assert and storage statements
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Later {
        fields {
            #[sharding(variable)] pub flag: bool,
            #[sharding(count)] pub tickets: nat,
            #[sharding(storage_option)] pub slot: Option<int>,
        }
        init! { initialize() { init flag = false; init tickets = 1; init slot = None; } }
        transition! { bad(value:int) {
            deposit slot += Some(value);
            remove tickets -= (1);
            update flag = true;
        } }
    }
}

} // verus!
fn main() {}
