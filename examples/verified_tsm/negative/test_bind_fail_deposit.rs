// EXPECTED-ERROR: pattern-binding cannot be used in a 'deposit' statement
//! Complete original bind_fail_deposit parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(storage_option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    deposit opt += Some(let x);
                }
            }
        }}

} // verus!
fn main() {}
