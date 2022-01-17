#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::construct_state_machine;

construct_state_machine!(
    state machine X {
        fields {
            #[sharding(variable)]
            counter: int,

            #[sharding(variable)]
            inc_a: bool,

            #[sharding(variable)]
            inc_b: bool,
        }

        #[invariant]
        #[spec]
        fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 } else { 0 }) + (if self.inc_b { 1 } else { 0 })
        }

        #[transition]
        fn tr_inc_a(&self, post: &X) {
            require(!self.inc_a);
            update(counter, self.counter + 1);
            update(inc_a, true);
        }
    }
);

fn main() { }
