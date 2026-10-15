// EXPECTED-ERROR: assertion failed
//! Complete original assert_let_fail_1_bind parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(variable)]
                pub opt: Option<int>,
            }

            transition!{
                tr1() {
                    assert let Option::Some(x) = pre.opt;
                }
            }
        }}

} // verus!
fn main() {}
