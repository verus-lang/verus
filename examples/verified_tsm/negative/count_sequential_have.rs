// EXPECTED-ERROR: verified backend requires have before add/remove on the same count field
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Sequential {
        fields { #[sharding(count)] pub tickets: nat, }
        init! { initialize() { init tickets = 1; } }
        transition! { consume_then_have() {
            remove tickets -= (1);
            have tickets >= (1);
        } }
    }
}

} // verus!
fn main() {}
