use vstd::cell::PCell;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_helpers as helpers;
use vstd::resource::tsm_storage::*;
verus! {

broadcast use {vstd::imap::group_imap_lemmas, vstd::iset::group_iset_lemmas};

pub struct Counts;

impl Machine for Counts {
    type Fragment = CountRA;

    type State = nat;

    open spec fn invariant(state: nat) -> bool {
        state <= 9
    }

    open spec fn embed(state: nat) -> CountRA {
        CountRA { count: state }
    }
}

impl StorageMachine for Counts {
    type Key = int;

    type Value = bool;

    open spec fn storage(state: nat) -> IMap<int, bool> {
        IMap::empty().insert(0int, true)
    }
}

pub proof fn ownership_history() {
    let tracked full = Token::<Counts>::alloc_state(9);
    assert(exists|remainder: CountRA|
        full.fragment() == CountRA::op(CountRA { count: 2 }, remainder)) by {
        assert(full.fragment() == CountRA::op(CountRA { count: 2 }, CountRA { count: 7 }));
    }
    let tracked (two, seven) = helpers::split_off(full, CountRA { count: 2 });
    assert(two.fragment().count == 2 && seven.fragment().count == 7);
    let tracked full = two.join(seven);
    assert(full.fragment().count == 9);
    let tracked stored = helpers::singleton_map(0int, true);
    let tracked full = StorageToken::<Counts>::alloc_state(9, stored);
    assert(exists|remainder: CountRA|
        full.fragment() == CountRA::op(CountRA { count: 2 }, remainder)) by {
        assert(full.fragment() == CountRA::op(CountRA { count: 2 }, CountRA { count: 7 }));
    }
    let tracked (two, seven) = helpers::split_off_storage(full, CountRA { count: 2 });
    assert(seven.fragment().count == 7);
    let tracked stored = helpers::guard_value(&two, 0int, true);
    assert(*stored);
    assert forall|frame: CountRA, state: nat|
        Counts::invariant(state) && CountRA::op(seven.fragment(), frame) == Counts::embed(
            state,
        ) implies exists|next: nat|
        Counts::invariant(next) && CountRA::op(CountRA { count: 6 }, frame) == Counts::embed(next)
            && Counts::storage(next) == Counts::storage(state).union_prefer_right(
            IMap::empty(),
        ).remove_keys(ISet::empty()) by {
        assert(Counts::storage(state).union_prefer_right(IMap::empty()).remove_keys(ISet::empty())
            =~= Counts::storage(state));
        let next = (state - 1) as nat;
        assert(state == 7 + frame.count);
        assert(Counts::invariant(next) && CountRA::op(CountRA { count: 6 }, frame) == Counts::embed(
            next,
        ));
    }
    let tracked (seven, withdrawn) = seven.exchange(
        IMap::tracked_empty(),
        CountRA { count: 6 },
        IMap::empty(),
    );
    assert(seven.fragment().count == 6);
    assert(*stored);
}

pub fn physical_map_round_trip() -> (out: u32)
    ensures
        out == 7,
{
    let (cell, Tracked(permission)) = PCell::new(7u32);
    let tracked map = helpers::singleton_map(0int, permission);
    let tracked permission = helpers::take_singleton(map, 0int);
    *cell.borrow(Tracked(&permission))
}

pub fn demonstration() -> (out: u32)
    ensures
        out == 7,
{
    proof {
        ownership_history();
    }
    physical_map_round_trip()
}

} // verus!
fn main() {
    assert_eq!(demonstration(), 7);
}
