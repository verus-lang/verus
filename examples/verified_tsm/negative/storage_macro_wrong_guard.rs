// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    WrongGuard {
        fields {
            #[sharding(variable)] pub owner: Option<int>,
            #[sharding(storage_option)] pub slot: Option<int>,
        }
        #[invariant] pub fn inv(&self)->bool { self.owner == self.slot }
        init! { initialize() { init owner = None; init slot = None; } }
        property! { wrong_guard() {
            require pre.owner == Some(1int);
            guard slot >= Some(2int);
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
    }
}

} // verus!
fn main() {}
