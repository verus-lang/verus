// EXPECTED-ERROR: expression has mode spec, expected mode proof
//! Both valid TransitionExample operations from the transition-language guide.
//! The invalid repeated update is tested separately.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  TransitionExample {
    fields {
        #[sharding(variable)]
        pub x: int,
        #[sharding(variable)]
        pub y: int,
    }

    init!{
        initialize(x: int, y: int) {
            init x = x;
            init y = y;
        }
    }

    // Okay.
    transition!{
        transition_1(x_new_value: int) {
            update x = x_new_value;
        }
    }

    // Okay.
    transition!{
        transition_2(b: bool) {
            if b {
                update x = 0;
                update y = 1;
            } else {
                update x = 5;
            }
        }
    }
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut x), Tracked(mut y)) =
            TransitionExample::Instance::initialize(8, 9);
        let ghost erased = x;
        let tracked recovered = erased;
        assert(x.value() == 3);
        assert(y.value() == 9);
        instance.transition_2(false, &mut x, &mut y);
        assert(x.value() == 5);
        assert(y.value() == 9);
        instance.transition_2(true, &mut x, &mut y);
        assert(x.value() == 0);
        assert(y.value() == 1);
    }
}

} // verus!
