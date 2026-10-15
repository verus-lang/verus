// EXPECTED-ERROR: transition name conflicts with a generated field facade method
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!( Sample {fields { #[sharding(variable)] pub value:int, } init!{initialize(){init value=0;}} transition!{change(){update value=1;}} transition!{__field_update_change(){update value=1;}}});
fn main() {}
