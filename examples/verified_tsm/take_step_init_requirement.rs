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
        let post = InitRequire::take_step::initialize(true, 9int);
        assert(post.n == 10 && post.invariant());
    }
}

} // verus!
