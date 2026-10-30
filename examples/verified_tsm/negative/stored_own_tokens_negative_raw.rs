// EXPECTED-ERROR: in a non-positive position
//! Raw route: negative occurrence of the protocol token in the payload.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {
pub tracked struct Payload { pub ghost f: spec_fn(C::Token) -> bool }
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    C {
        fields {
            #[sharding(bool)]
            pub flag: bool,

            #[sharding(storage_option)]
            pub store: Option<Payload>,
        }

        init!{
            initialize() {
                init flag = true;
                init store = None;
            }
        }
    }
}

fn main() {}
