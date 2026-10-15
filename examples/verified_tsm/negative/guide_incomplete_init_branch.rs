// EXPECTED-ERROR: both branches of an if-statement must initialize the same fields
//! Invalid branch initialization example from the transition-language reference.
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
        init! { initialize_3(b: bool) {
            if b {
                init x = 0;
                init y = 1;
            } else {
                init x = 5;
            }
        } }
    }
}

fn main() {
}

} // verus!
