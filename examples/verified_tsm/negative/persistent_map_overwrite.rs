// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    CannotRewrite {
        fields {
            #[sharding(persistent_imap)] pub entries:IMap<nat,int>,
        }
        init! { initialize() { init entries=IMap::empty().insert(0nat,7int); } }
        transition! { overwrite() { add entries (union)= [0nat=>8int]; } }
    }
}

} // verus!
fn main() {}
