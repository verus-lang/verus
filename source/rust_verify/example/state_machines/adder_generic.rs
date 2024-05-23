#[allow(unused_imports)]
use builtin::*;
use vstd::{pervasive::*, *};

use state_machines_macros::state_machine;

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
