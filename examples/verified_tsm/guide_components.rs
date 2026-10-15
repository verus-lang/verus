//! Complete AdderMachine snippet from the guide's components chapter.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine!{

    AdderMachine {
        //// The state definition

        fields {
            #[sharding(variable)]
            pub number: int,
        }

        //// The transitions

        init!{
            initialize() {
                init number = 0;
            }
        }

        transition!{
            add(n: int) {
                update number = pre.number + 2*n;
            }
        }

        //// Invariants on the state

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        //// Proofs that the invariants hold

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            // Verus proves that 0 % 2 == 0
        }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: int) {
            // Verus proves that if `pre.number % 2 == 0` then
            // `post.number` is `pre.number + 2*n` is divisble by 2 as well.
        }
    }
}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut number)) = AdderMachine::Instance::initialize();
        instance.add(4, &mut number);
        instance.add(-3, &mut number);
        assert(number.value() == 2);
    }
}

} // verus!
