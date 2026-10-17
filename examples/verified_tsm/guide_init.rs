//! Valid InitExample from the transition-language reference.
//! Its two invalid initialization examples are separate negative cases.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine! {  InitExample {
    fields {
        #[sharding(variable)]
        pub x: int,
        #[sharding(variable)]
        pub y: int,
    }

    // Okay.
    init!{
        initialize_1(x_init_value: int) {
            init x = x_init_value;
            init y = 0;
        }
    }
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(x), Tracked(y)) =
            InitExample::Instance::initialize_1(7);
        assert(x.value() == 7);
        assert(y.value() == 0);
    }
}

} // verus!
