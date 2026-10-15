// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ InitRequire {
    fields {pub n: int}
    init!{ initialize(b: bool, n: int) {
        require b;
        let value: int = n + 1;
        init n = value;
    } }
}}

fn main() {
    proof {
        assert(!InitRequire::State::initialize_enabled(false, 9int));
        let post = InitRequire::take_step::initialize(false, 9int);
    }
}

} // verus!
