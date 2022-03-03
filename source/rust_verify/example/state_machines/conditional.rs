#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            pub a: int,

            #[sharding(variable)]
            pub b: int,

            #[sharding(variable)]
            pub c: int,
        }

        #[init]
        fn initialize(&self, cond: bool) {
            init(a, 0);
            init(b, 1);
            if cond {
                init(c, 2);
            } else {
                init(c, 3);
            }
        }

        #[transition]
        fn add(&self, n: int) {
            update(a, 0);
            if n >= 0 {
                update(b, self.b + n);
            } else {
                update(b, self.b - n);
                update(c, 15);
            }
        }

        #[transition]
        fn add2(&self, n: int) {
            update(a, 0);
            if n >= 0 {
                update(c, 15);
                update(b, self.b + n);
            } else {
                update(b, self.b - n);
            }
        }

       
        #[inductive(initialize)]
        fn initialize_inductive(post: X, cond: bool) { }
     
        #[inductive(add)]
        fn add_inductive(self: X, post: X, n: int) { }
     
        #[inductive(add2)]
        fn add2_inductive(self: X, post: X, n: int) { }

    }
);

fn main() { }
