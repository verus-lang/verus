// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(take)]
    Hidden {
        fields {
            #[sharding(variable)] pub flag: bool,
            #[sharding(storage_option)] pub storage: Option<nat>,
        }
        init! { initialize() {init flag=false;init storage=Some(7nat);} }
        transition! { take() {
            withdraw storage-=Some(let value);
            update flag=true;
        } }
    }
}

} // verus!
fn main() {}
