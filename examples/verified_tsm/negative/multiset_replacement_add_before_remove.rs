// EXPECTED-ERROR: verified option/map/multiset replacement must remove then add on each modifying path
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 WrongOrder {
    fields {#[sharding(multiset)] pub bag:Multiset<int>,}
    init! {initialize(){init bag=Multiset::empty().insert(10int);}}
    transition! {wrong(){add bag += {12int};remove bag -= {10int};}}
} }
fn main() {}
