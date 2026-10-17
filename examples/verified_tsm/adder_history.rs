//! Complete ordinary adder.rs model, including its local initialization let.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(

    X {
        fields {
            #[sharding(variable)]
            pub number: int,
        }

        init!{
            initialize() {
                let x = 5 + 9;
                init number = 0;
            }
        }

        transition!{
            add(n: int) {
                require n == 0;
                update number = pre.number + 2*n;
            }
        }

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: int) {
        }

    }
);

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut number)) = X::Instance::initialize();
        instance.add(0, &mut number);
        assert(number.value() == 0);
    }
}

} // verus!
