// EXPECTED-ERROR: in a non-positive position
//! Raw route: token as an IMap key (IMap rejects recursive K).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::imap::IMap;

verus! {
pub tracked struct Payload { pub ghost f: IMap<C::Token, bool> }
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
