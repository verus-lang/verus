//! Nondeterministic operations preserve their explicitly borrowed input.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_storage::*;

verus! {

broadcast use {vstd::iset::group_iset_lemmas, vstd::imap::group_imap_lemmas};

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

proof fn update_preserves_shared() {
    let tracked all = Token::<Bounded>::alloc_state(2);
    let tracked (owned, shared) = all.split(CountRA { count: 1 }, CountRA { count: 1 });
    let outputs = ISet::new(|new: CountRA| new.count == 0 || new.count == 1);
    let lifted = outputs.map(|new: CountRA| CountRA::op(new, shared.fragment()));
    assert(outputs.contains(CountRA { count: 0 }));
    assert(lifted.contains(CountRA { count: 1 }));
    assert(frame_update_nondeterministic::<Bounded>(
        CountRA::op(owned.fragment(), shared.fragment()),
        lifted,
    )) by {
        assert forall|frame: CountRA, state: nat|
            Bounded::invariant(state) && CountRA::op(
                CountRA::op(owned.fragment(), shared.fragment()),
                frame,
            ) == Bounded::embed(state) implies exists|new: CountRA, next: nat|
            lifted.contains(new) && Bounded::invariant(next) && CountRA::op(new, frame)
                == Bounded::embed(next) by {
            assert(frame.count == 0);
            assert(lifted.contains(CountRA { count: 1 }) && Bounded::invariant(1) && CountRA::op(
                CountRA { count: 1 },
                frame,
            ) == Bounded::embed(1));
        }
    };
    let tracked owned = owned.update_nondeterministic_with_shared(&shared, outputs);
    assert(owned.fragment().count == 0 || owned.fragment().count == 1);
    assert(shared.fragment().count == 1);
    let tracked all = owned.join(shared);
    assert(all.fragment().count == 1 || all.fragment().count == 2);
}

proof fn exchange_preserves_shared() {
    let tracked all = StorageToken::<Bounded>::alloc_state(2, IMap::tracked_empty());
    let tracked (owned, shared) = all.split(CountRA { count: 1 }, CountRA { count: 1 });
    let outputs = ISet::new(
        |pair: (CountRA, IMap<int, bool>)|
            (pair.0.count == 0 || pair.0.count == 1) && pair.1 == IMap::empty(),
    );
    let lifted = outputs.map(
        |pair: (CountRA, IMap<int, bool>)| (CountRA::op(pair.0, shared.fragment()), pair.1),
    );
    assert(outputs.contains((CountRA { count: 0 }, IMap::empty())));
    assert(lifted.contains((CountRA { count: 1 }, IMap::empty())));
    assert(frame_exchange_nondeterministic::<Bounded>(
        CountRA::op(owned.fragment(), shared.fragment()),
        IMap::empty(),
        lifted,
    )) by {
        assert forall|frame: CountRA, state: nat|
            Bounded::invariant(state) && CountRA::op(
                CountRA::op(owned.fragment(), shared.fragment()),
                frame,
            ) == Bounded::embed(state) implies exists|
            new: CountRA,
            withdraw: IMap<int, bool>,
            next: nat,
        |
            {
                &&& lifted.contains((new, withdraw))
                &&& Bounded::invariant(next)
                &&& CountRA::op(new, frame) == Bounded::embed(next)
                &&& Bounded::storage(state).dom().disjoint(IMap::<int, bool>::empty().dom())
                &&& Bounded::storage(next).dom().disjoint(withdraw.dom())
                &&& Bounded::storage(state).union_prefer_right(IMap::empty()) =~= Bounded::storage(
                    next,
                ).union_prefer_right(withdraw)
            } by {
            assert(frame.count == 0);
            assert(lifted.contains((CountRA { count: 1 }, IMap::empty())) && Bounded::invariant(1)
                && CountRA::op(CountRA { count: 1 }, frame) == Bounded::embed(1));
        }
    };
    let tracked (owned, withdrawn) = owned.exchange_nondeterministic_with_shared(
        &shared,
        IMap::tracked_empty(),
        outputs,
    );
    assert(withdrawn == IMap::empty());
    assert(owned.fragment().count == 0 || owned.fragment().count == 1);
    assert(shared.fragment().count == 1);
    let tracked all = owned.join(shared);
    assert(all.fragment().count == 1 || all.fragment().count == 2);
}

fn main() {
}

} // verus!
