use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model! { X {
    fields { #[sharding(variable)] pub number: int, }
    init! { initialize() { init number = 0; } }
    property! { observation() { assert(pre.number == pre.number); } }
}}

proof fn bad() {
    let s = X::Step::observation();
}

fn main() {
}

} // verus!
