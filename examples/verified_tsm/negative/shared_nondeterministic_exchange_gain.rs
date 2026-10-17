// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm::*;
use vstd::resource::tsm_storage::*;
#[path = "../shared_nondeterministic.rs"]
mod model;

verus! {

proof fn invalid_gain() {
    let tracked all = StorageToken::<model::Bounded>::alloc_state(2, IMap::tracked_empty());
    let tracked (owned, shared) = all.split(CountRA { count: 1 }, CountRA { count: 1 });
    let outputs = ISet::new(
        |pair: (CountRA, IMap<int, bool>)| pair.0.count == 2 && pair.1 == IMap::empty(),
    );
    let tracked invalid = owned.exchange_nondeterministic_with_shared(
        &shared,
        IMap::tracked_empty(),
        outputs,
    );
}

fn main() {
}

} // verus!
