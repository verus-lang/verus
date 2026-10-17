// EXPECTED-ERROR: field 'x' might be updated multiple times
//! Invalid repeated update from the transition-language reference.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    TransitionExample {
        fields { #[sharding(variable)] pub x: int, }
        transition! { transition_3(b: bool) {
            update x = 0;
            update x = 1;
        } }
    }
}

fn main() {
}

} // verus!
