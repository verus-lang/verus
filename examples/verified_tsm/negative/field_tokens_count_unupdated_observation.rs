// EXPECTED-ERROR: Count facade requires every ordinary observation to be updated
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! { C {fields {#[sharding(variable)] pub flag:bool,#[sharding(variable)] pub other:bool,#[sharding(count)] pub c:nat,#[sharding(count)] pub d:nat,}init!{initialize(){init flag=false;init other=false;init c=1;init d=0;}}transition!{change(){require(!pre.other);remove c -= (1);add d += (1);update flag=true;}}}}
fn main() {}
