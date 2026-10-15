// EXPECTED-ERROR: for the persistent strategy `persistent_bool`, use `(union)=` instead of `+=`
//! Complete original use_plus_for_persistent_fail parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(persistent_bool)]
                pub c: bool,
            }

            transition!{
                tr_add() {
                    add c += true;
                }
            }
        }}

} // verus!
fn main() {}
