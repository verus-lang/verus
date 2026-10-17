//! Shared validation observes the separating composition of two storage tokens.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_storage::*;

verus! {

pub struct Bounded;

impl Machine for Bounded {
    type Fragment = CountRA;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        state <= 2
    }

    open spec fn embed(state: nat) -> CountRA {
        CountRA { count: state }
    }
}

impl StorageMachine for Bounded {
    type Key = int;

    type Value = bool;

    open spec fn storage(state: nat) -> IMap<int, bool> {
        IMap::empty()
    }
}

proof fn validate_owned_with_shared() {
    let tracked all = StorageToken::<Bounded>::alloc_state(2, IMap::tracked_empty());
    let tracked (mut owned, shared) = all.split(CountRA { count: 1 }, CountRA { count: 1 });
    owned.validate();
    // A completion of just the owned token could have state count one.
    assert(Bounded::invariant(1));
    assert(CountRA::op(owned.fragment(), CountRA { count: 0 }) == Bounded::embed(1));

    owned.validate_2(&shared);
    assert(owned.fragment().count == 1);
    assert(shared.fragment().count == 1);
    let (frame, state) = choose|frame: CountRA, state: nat|
        Bounded::invariant(state) && CountRA::op(
            CountRA::op(owned.fragment(), shared.fragment()),
            frame,
        ) == Bounded::embed(state);
    // Validation with the shared token observes both counts, ruling out state one.
    assert(state == 2);
    assert(frame.count == 0);
}

fn main() {
}

} // verus!
