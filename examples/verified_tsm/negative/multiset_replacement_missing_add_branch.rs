// EXPECTED-ERROR: verified replacement requires both remove and add on each modifying path
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 MissingAdd {
    fields {#[sharding(multiset)] pub bag:Multiset<int>,}
    init! {initialize(){init bag=Multiset::empty().insert(10int);}}
    transition! {wrong(add_back:bool){
        remove bag -= {10int};
        if add_back {add bag += {12int};}
    }}
} }
fn main() {}
