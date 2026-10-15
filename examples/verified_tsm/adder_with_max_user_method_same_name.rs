// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

pub struct Payload {
    pub value: int,
}

impl Payload {
    pub open spec fn minimum(&self) -> int {
        self.value
    }
}

} // verus!
verified_tokenized_state_machine! {

    AdderWithMax {
        fields {
            #[sharding(constant)]
            pub maximum: int,

            #[sharding(variable)]
            pub number: int,

            #[sharding(not_tokenized)]
            pub minimum: int,
        }

        init!{
            initialize(m: Payload) {
                require(m.minimum() >= 0);
                init number = m.minimum();
                init minimum = m.minimum();
                init maximum = m.minimum();
            }
        }

        transition!{
            add(n: int) {
                require(n >= 0);
                require(pre.number + n <= pre.maximum);
                update number = pre.number + n;
            }
        }

        transition!{
            change_to_minimum() {
                birds_eye let min = pre.minimum;
                update number = min;
            }
        }

        #[invariant]
        pub fn is_bounded_below(&self) -> bool {
            self.number >= self.minimum
        }

        #[invariant]
        pub fn is_bounded_above(&self) -> bool {
            self.number <= self.maximum
        }

        #[inductive(initialize)]
        fn init_preserves(post: Self, m: Payload) {
        }

        #[inductive(add)]
        fn add_preserves(pre: Self, post: Self, n: int) {
        }

        #[inductive(change_to_minimum)]
        fn change_to_minimum_inductive(pre: Self, post: Self) { }
    }
}

verus! {

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut number)) = AdderWithMax::Instance::initialize(
            Payload { value: 3int },
        );
        assert(number.value() == 3int);
        instance.change_to_minimum(&mut number);
        assert(number.value() == 3int);
    }
}

} // verus!
