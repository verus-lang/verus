use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine! {

    Y {
        fields {
            #[sharding(variable)]
            pub x: int,
            #[sharding(variable)]
            pub y: int,
        }

        #[invariant]
        pub fn ordered(&self) -> bool {
            self.x <= self.y
        }

        init! {
            initialize() {
                init x = 0;
                init y = 0;
            }
        }

        transition! {
            decrement() {
                let value = pre.x - 1;
                update x = value;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(decrement)]
        fn decrement_inductive(pre: Self, post: Self) {}
    }
}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut x), Tracked(y)) = Y::Instance::initialize();
        inst.decrement(&mut x);
        assert(x.value() == -1);
        assert(y.value() == 0);
        inst.decrement(&mut x);
        assert(x.value() == -2);
        assert(y.value() == 0);
    }
}

} // verus!
