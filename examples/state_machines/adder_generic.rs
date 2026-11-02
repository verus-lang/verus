// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
use vstd::{pervasive::*, *};

#[cfg(not(verus_verified_tsm))]
use verus_state_machines_macros::state_machine;
#[cfg(verus_verified_tsm)]
use verus_state_machines_macros::verified_state_machine_model as state_machine;

state_machine!(
    X<T> {
        fields {
            pub number: int,
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

fn main() {}
