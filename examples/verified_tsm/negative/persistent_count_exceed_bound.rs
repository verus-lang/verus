// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm::*;
use vstd::resource::tsm_persistent::*;
#[path = "../persistent_count_algebra.rs"]
mod lower_bounds;

verus! {

proof fn exceed_the_invariant_bound() {
    let tracked token = Token::<lower_bounds::Bounded>::alloc_state(3);
    let tracked invalid = token.update(PersistentCountRA { count: 11 });
}

fn main() {
}

} // verus!
