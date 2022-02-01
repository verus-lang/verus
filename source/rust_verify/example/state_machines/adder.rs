#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::construct_state_machine;

construct_state_machine!(
    state machine X {
        fields {
            number: int,
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
        fn init_preserves(self: X, post: X) {
        }

        #[inductive(add)]
        fn add_preserves(self: X, post: X, n: int) {
        }
    }
);

fn main() { }
