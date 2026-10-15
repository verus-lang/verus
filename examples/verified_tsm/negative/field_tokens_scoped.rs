// EXPECTED-ERROR: field facade currently supports straight-line ordinary fields
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!( Sample {fields { #[sharding(variable)] pub value:int, } init!{initialize(){init value=0;}} transition!{change(){if pre.value==0 {update value=1;} else {update value=0;}}}});
fn main() {}
