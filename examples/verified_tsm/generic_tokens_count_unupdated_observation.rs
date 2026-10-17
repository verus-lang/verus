//! An operation that reads a variable it does not update, next to count updates.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! { C {
    fields {
        #[sharding(variable)] pub flag: bool,
        #[sharding(variable)] pub other: bool,
        #[sharding(count)] pub c: nat,
        #[sharding(count)] pub d: nat,
    }
    init!{ initialize() { init flag = false; init other = false; init c = 1; init d = 0; } }
    transition!{ change() { require(!pre.other); remove c -= (1); add d += (1); update flag = true; } }
}}

proof fn test() {
    let tracked (Tracked(inst), Tracked(mut flag), Tracked(other), Tracked(c), Tracked(_d)) =
        C::Instance::initialize();
    let tracked d = inst.change(&mut flag, &other, c);
    assert(flag.value() && !other.value());
    assert(d.count() == 1);
}

fn main() {
    proof { test(); }
}

} // verus!
