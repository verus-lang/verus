//! A borrowed count, a produced count and an updated variable in one operation.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! { C {
    fields {
        #[sharding(variable)] pub flag: bool,
        #[sharding(count)] pub c: nat,
        #[sharding(count)] pub d: nat,
    }
    init!{ initialize() { init flag = false; init c = 1; init d = 0; } }
    transition!{ change() { have c >= (1); add d += (1); update flag = true; } }
}}

proof fn test() {
    let tracked (Tracked(inst), Tracked(mut flag), Tracked(c), Tracked(_d)) = C::Instance::initialize();
    let tracked d = inst.change(&mut flag, &c);
    assert(flag.value());
    assert(c.count() == 1 && d.count() == 1);
}

fn main() {
    proof { test(); }
}

} // verus!
