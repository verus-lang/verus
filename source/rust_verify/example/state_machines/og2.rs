#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::concurrent_state_machine;

concurrent_state_machine!(
    X {
        fields {
            #[sharding(variable)]
            counter: int,

            #[sharding(variable)]
            inc_a: bool,

            #[sharding(variable)]
            inc_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 } else { 0 }) + (if self.inc_b { 1 } else { 0 })
        }

        #[init]
        fn initialize(&self) {
            update(counter, 0);
            update(inc_a, false);
            update(inc_b, false);
        }

        #[transition]
        fn tr_inc_a(&self) {
            require(!self.inc_a);
            update(counter, self.counter + 1);
            update(inc_a, true);
        }

        #[transition]
        fn tr_inc_b(&self) {
            require(!self.inc_b);
            update(counter, self.counter + 1);
            update(inc_b, true);
        }

        #[readonly]
        fn finalize(&self) {
            require(self.inc_a);
            require(self.inc_b);
            assert(self.counter == 2);
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(self: X, post: X) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(self: X, post: X) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: X) {
        }

        #[safety(finalize_safety_1)]
        fn finalize_correct(pre: X) {
            // XXX TODO verus currently doesn't generate the right conditions here
        }
    }
);

fn main() { }
