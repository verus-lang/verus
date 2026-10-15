// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::{CountRA, Machine};
use vstd::resource::tsm_storage::*;
verus! {

pub struct Boolean;

impl Machine for Boolean {
    type Fragment = CountRA;

    type State = bool;

    open spec fn invariant(s: bool) -> bool {
        true
    }

    open spec fn embed(s: bool) -> CountRA {
        CountRA {
            count: if s {
                1nat
            } else {
                0nat
            },
        }
    }
}

impl StorageMachine for Boolean {
    type Key = int;

    type Value = bool;

    open spec fn storage(s: bool) -> IMap<int, bool> {
        IMap::empty()
    }
}

proof fn misuse() {
    let tracked token = StorageToken::<Boolean>::alloc_state(true, IMap::tracked_empty());
    let tracked (owned, reading) = token.split(CountRA { count: 1 }, CountRA { count: 0 });
    let tracked observation = reading.observe();
    let outputs = ISet::new(
        |pair: (CountRA, IMap<int, bool>)|
            pair.0.count == 2 && pair.1 == IMap::<int, bool>::empty(),
    );
    let tracked bad = owned.exchange_nondeterministic_with_observation(
        &observation,
        IMap::tracked_empty(),
        outputs,
    );
}

fn main() {
}

} // verus!
