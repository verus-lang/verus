// EXPECTED-ERROR: stored-resource bindings must precede physical storage modifications
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 LaterBinding {
    fields {#[sharding(storage_imap)] pub stored:IMap<nat,nat>,}
    init! {initialize(){init stored=IMap::empty();}}
    transition! {later(){
        deposit stored += [1nat=>43nat];
        withdraw stored -= [1nat=>let permission];
    }}
} }

} // verus!
fn main() {}
