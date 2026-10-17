// EXPECTED-ERROR: assertion failed
//! Owning an empty set fragment cannot establish absence from other owners.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
BlindSetAddition {
    fields { #[sharding(iset)] pub permissions: ISet<int>, }
    init! { initialize() { init permissions = ISet::empty(); } }
    transition! { unsafe_add() {
        add permissions += (ISet::empty().insert(1int));
    } }
});

} // verus!
fn main() {}
