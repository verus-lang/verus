#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::state_machine;

state_machine!(
    X {
        fields {
            pub number: int,
        }

        #[init]
        fn initialize(&self) {
            update(number, 0);
        }

        #[transition]
        fn add(&self, n: int) {
            update(number, self.number + 2*n);
        }

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: X) { }

        #[inductive(add)]
        fn add_inductive(self: X, post: X, n: int) { }
    }
);

fn main() { }
