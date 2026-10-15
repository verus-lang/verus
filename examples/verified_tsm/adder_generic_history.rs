//! Complete generic even-number adder model from state_machines/adder_generic.rs.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine!(

    X<T> {
        fields {
            #[sharding(variable)]
            pub number: int,
            #[sharding(variable)]
            pub t: T,
        }

        init!{
            initialize(t: T) {
                init number = 0;
                init t = t;
            }
        }

        transition!{
            add(n: int) {
                update number = pre.number + 2*n;
            }
        }

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        #[inductive(initialize)]
        fn init_preserves(post: Self, t: T) {
        }

        #[inductive(add)]
        fn add_preserves(pre: Self, post: Self, n: int) {
        }
    }
);

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut number), Tracked(t)) = X::Instance::<
            u64,
        >::initialize(7);
        instance.add(3, &mut number);
        instance.add(-5, &mut number);
        assert(number.value() == -4);
        assert(t.value() == 7);
    }
}

} // verus!
