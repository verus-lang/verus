#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::construct_state_machine;

construct_state_machine!(
    state machine X {
        fields {
            #[sharding(variable)]
            number: int,
        }

        #[init]
        #[spec]
        fn initialize(&self) {
            update(number, 0);
        }

        #[transition]
        #[spec]
        fn add(&self, n: int) {
            update(number, self.number + 2*n);
        }

        #[invariant]
        #[spec]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        #[proof]
        #[inductive(initialize)]
        fn init_preserves(self: X, post: X) {
        }

        #[proof]
        #[inductive(add)]
        fn add_preserves(self: X, post: X, n: int) {
        }
    }
);

fn main() { }
