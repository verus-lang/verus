// EXPECTED-ERROR: cannot name a transition parameter of the checked macro
//! Transition parameters may not use the names of the generated raw operations' parameters
//! and binders (`owned`, `h`, `z`, `new`, `shared`, `out`, `result`, `outputs`), which they
//! would duplicate or shadow.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    X {
        fields {
            #[sharding(map)] pub m: Map<int, int>,
        }
        init! { initialize() { init m = Map::empty(); } }
        transition! { t(z: int) {
            remove m -= [z => 0];
            add m += [z => 1];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(t)] fn t_inductive(pre: Self, post: Self, z: int) {}
    }
}

fn main() {}
} // verus!
