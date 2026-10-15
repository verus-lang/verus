// EXPECTED-ERROR: at most one deposit and one withdraw, or one guard, on each execution path
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 DuplicateDeposit {
    fields {#[sharding(storage_imap)] pub stored:IMap<nat,nat>,}
    init! {initialize(){init stored=IMap::empty();}}
    transition! {duplicate(){
        deposit stored += [0nat=>43nat];
        deposit stored += [1nat=>44nat];
    }}
} }

} // verus!
fn main() {}
