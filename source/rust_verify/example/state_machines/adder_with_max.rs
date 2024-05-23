#[allow(unused_imports)]
use builtin::*;
use vstd::{pervasive::*, *};

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine! {
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
            initialize(m: int) {
                require(m >= 0);
                init number = 0;
                init minimum = 0;
                init maximum = m;
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
        fn init_preserves(post: Self, m: int) {
        }

        #[inductive(add)]
        fn add_preserves(pre: Self, post: Self, n: int) {
        }

        #[inductive(change_to_minimum)]
        fn change_to_minimum_inductive(pre: Self, post: Self) { }
    }
}

fn main() {}
