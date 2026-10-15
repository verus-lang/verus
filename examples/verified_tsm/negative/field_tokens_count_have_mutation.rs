// EXPECTED-ERROR: Count facade currently supports consuming and producing count owners
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! { C {fields {#[sharding(variable)] pub flag:bool,#[sharding(count)] pub c:nat,#[sharding(count)] pub d:nat,}init!{initialize(){init flag=false;init c=1;init d=0;}}transition!{change(){have c >= (1);add d += (1);update flag=true;}}}}
fn main() {}
