// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm::*;
#[path = "../shared_nondeterministic.rs"]
mod model;

verus! {

proof fn invalid_gain() {
    let tracked all = Token::<model::Bounded>::alloc_state(2);
    let tracked (owned, shared) = all.split(CountRA { count: 1 }, CountRA { count: 1 });
    // Owned count two plus the unchanged shared count one violates the bound.
    let outputs = ISet::new(|new: CountRA| new.count == 2);
    let tracked invalid = owned.update_nondeterministic_with_shared(&shared, outputs);
}

fn main() {
}

} // verus!
