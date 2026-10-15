// EXPECTED-ERROR: assertion failed
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 X {
    fields {
        #[sharding(variable)] pub x: int,
        #[sharding(persistent_bool)] pub flag: bool,
    }
    init! { initialize() { init x = 0; init flag = false; } }
    transition! { advance() { assert false; update x = pre.x + 1; } }
    #[invariant] pub fn nonnegative(&self) -> bool { self.x >= 0 }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(advance)] fn advance_inductive(pre: Self, post: Self) {}
}}
fn main() {}
