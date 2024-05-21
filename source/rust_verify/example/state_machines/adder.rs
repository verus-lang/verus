#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*, *};

use state_machines_macros::state_machine;

verus! {

state_machine!(
    X {
        fields {
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

} // verus!
fn main() {}
