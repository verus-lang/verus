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

        /*#[inductive(initialize)]
        fn init_preserves(post: X) {
        }*/

        /*#[inductive(add)]
        fn add_preserves(self: X, post: X, n: int) {
        }*/

        /*#[inductive(initialize)]
        fn initialize_inductive() { }

        #[inductive(add)]
        fn add_inductive(n: int) { }*/

        #[inductive(initialize)]
        fn initialize_inductive(self: X, post: X) { }

        #[inductive(add)]
        fn add_inductive(post: X, n: int) { }

    }
);

fn main() { }
