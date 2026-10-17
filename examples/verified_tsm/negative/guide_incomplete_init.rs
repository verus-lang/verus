// EXPECTED-ERROR: does not initialize field 'y'
//! Invalid initialization example from the transition-language reference.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    InitExample {
        fields {
            #[sharding(variable)] pub x: int,
            #[sharding(variable)] pub y: int,
        }
        init! { initialize_2(x_init_value: int) {
            init x = x_init_value;
        } }
    }
}

fn main() {
}

} // verus!
