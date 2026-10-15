// EXPECTED-ERROR: transition parameter conflicts with a field-token argument
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!( Sample {fields { #[sharding(variable)] pub value:int, } init!{initialize(){init value=0;}} transition!{change(value:int){update value=value;}}});
fn main() {}
