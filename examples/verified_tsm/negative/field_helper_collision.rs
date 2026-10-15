// EXPECTED-ERROR: field names conflict with generated field helpers
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Ambiguous {
        fields {
            #[sharding(constant)] pub label: int,
            #[sharding(variable)] pub counter: int,
            #[sharding(variable)] pub counter_with_constants: int,
        }
        init! { initialize() {
            init label=0;
            init counter=0;
            init counter_with_constants=0;
        } }
    }
}

} // verus!
fn main() {}
