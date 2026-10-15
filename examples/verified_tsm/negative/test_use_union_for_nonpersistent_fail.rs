// EXPECTED-ERROR: use `+=` instead of `(union)=`
//! Complete original use_union_for_nonpersistent_fail parser/safety negative.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{
    #[verified_raw_tokens]
 Y {
            fields {
                #[sharding(bool)]
                pub c: bool,
            }

            transition!{
                tr_add() {
                    add c (union)= true;
                }
            }
        }}

} // verus!
fn main() {}
