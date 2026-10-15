// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {

    AdderWithMax {
        fields {
            #[sharding(constant)]
            pub maximum: int,

            #[sharding(variable)]
            pub number: int,

            #[sharding(not_tokenized)]
            pub minimum: IMap<int,int>,
        }

        init!{
            initialize(m: int) {
                require(m >= 0);
                init number = 0;
                init minimum = IMap::<int,int>::empty();
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
                update minimum[0int] = 0int;
                update number = 0;
            }
        }

        #[invariant]
        pub fn is_bounded_below(&self) -> bool {
            self.number >= 0
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
