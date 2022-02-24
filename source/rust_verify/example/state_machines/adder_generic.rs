#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::state_machine;

state_machine!(
    X<T> {
        fields {
            pub number: int,
            pub t: T,
        }

        #[init]
        fn initialize(&self, t: T) {
            init(number, 0);
            init(t, t);
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
        fn init_preserves(post: X<T>, t: T) {
        }

        #[inductive(add)]
        fn add_preserves(self: X<T>, post: X<T>, n: int) {
        }
    }
);

fn main() { }
