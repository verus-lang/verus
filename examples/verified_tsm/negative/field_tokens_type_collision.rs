// EXPECTED-ERROR: field token name conflicts with a generated machine type
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!( Sample {fields { #[sharding(variable)] pub Instance:int, } init!{initialize(){init Instance=0;}}});
fn main() {}
