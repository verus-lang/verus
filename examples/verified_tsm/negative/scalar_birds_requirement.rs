// EXPECTED-ERROR: preconditions of an exchange cannot depend on such bindings
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
HiddenRequirement {
    fields {
        #[sharding(variable)] pub visible: int,
        #[sharding(not_tokenized)] pub hidden: int,
    }
    init! { initialize() { init visible = 0; init hidden = 0; } }
    transition! { bad() {
        birds_eye let selected = pre.hidden;
        require selected >= 0;
        update visible = selected;
    } }
});

} // verus!
fn main() {}
