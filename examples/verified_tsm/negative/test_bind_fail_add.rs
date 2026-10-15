// EXPECTED-ERROR: pattern-binding cannot be used in an 'add' statement
//! Complete original bind_fail_add parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(option)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    add opt += Some(let x);
                }
            }
        }}

} // verus!
fn main() {}
