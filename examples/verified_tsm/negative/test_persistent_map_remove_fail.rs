// EXPECTED-ERROR: a persistent field's value can only grow, never remove or modify its data
//! Complete original persistent_map_remove_fail parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(persistent_imap)]
                pub c: IMap<int, int>,
            }

            transition!{
                tr_remove() {
                    remove c -= [1 => 2];
                }
            }
        }}

} // verus!
fn main() {}
