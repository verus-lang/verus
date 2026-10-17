// EXPECTED-ERROR: assertion failed
//! Original unconditional set Add cannot prove global absence.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{iset::*, set::*};
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
Original {
    fields {#[sharding(set)] pub b:Set<int>}
    transition! {tr_add() {add b += set { 5 };}}
}}

} // verus!
fn main() {}
