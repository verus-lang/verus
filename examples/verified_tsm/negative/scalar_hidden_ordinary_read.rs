// EXPECTED-ERROR: unowned fields cannot be read by a token operation
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
HiddenOrdinaryRead {
    fields {
        #[sharding(variable)] pub visible: int,
        #[sharding(not_tokenized)] pub hidden: int,
    }
    init! { initialize() { init visible = 0; init hidden = 0; } }
    transition! { bad() {
        let selected = pre.hidden;
        update visible = selected;
    } }
});

} // verus!
fn main() {}
