#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;

use state_machines_macros::construct_state_machine;

construct_state_machine!(
    state machine X {
        #[invariant]
        #[spec]
        fn stuff(&self) -> bool {
            true
        }
    }
);

fn main() { }
