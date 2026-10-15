// EXPECTED-ERROR: postcondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Unsafe {
        fields { #[sharding(variable)] pub value: int, }
        #[invariant] pub fn nonnegative(&self) -> bool { self.value >= 0 }
        init! { initialize() { init value = 0; } }
        transition! { break_invariant() { update value = -1; } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(break_invariant)] fn broken(pre: Self, post: Self) {}
    }
}

} // verus!
fn main() {}
