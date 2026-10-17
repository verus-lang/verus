// EXPECTED-ERROR: constant getter conflicts with a generated field facade method
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! { C {fields {#[sharding(constant)] pub clone:nat,#[sharding(count)] pub c:nat,}init!{initialize(){init clone=0;init c=0;}}}}
fn main() {}
