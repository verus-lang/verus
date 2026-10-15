// EXPECTED-ERROR: assertion failed
//! Original unconditional Add has no invariant proving absence.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
Original {
    fields {#[sharding(bool)] pub b:bool}
    transition! {tr_add() {
                    add b += true by {
                        assert(pre.b == false); // EXPECTED-ERROR: assertion failed
                    };
    }}
}}

} // verus!
fn main() {}
