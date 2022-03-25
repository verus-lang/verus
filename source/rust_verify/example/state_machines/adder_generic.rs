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
        fn init_preserves(post: X<T>, t: T) {
        }

        #[inductive(add)]
        fn add_preserves(pre: X<T>, post: X<T>, n: int) {
        }
    }
);

fn main() { }
