// EXPECTED-ERROR: assertion failed
//! A later requirement cannot discharge an earlier assertion.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BadOrder {
        fields { #[sharding(variable)] pub value:nat, }
        init! { initialize() {init value=0;} }
        transition! { bad() {
            let value=pre.value;
            assert value==1;
            require value==1;
            update value=1;
        } }
    }
}

} // verus!
fn main() {}
