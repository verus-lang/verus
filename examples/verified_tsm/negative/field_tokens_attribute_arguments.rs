// EXPECTED-ERROR: field facade attribute takes no arguments
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!(#[verified_field_tokens(change)] Sample {fields { #[sharding(variable)] pub value:int, } init!{initialize(){init value=0;}}});
fn main(){}
