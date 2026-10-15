//! Move a logical map entry to a different key while observing a borrowed entry.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::tsm_collections::*;
verus! {

pub open spec fn entries_at(phase: int) -> IMap<int, int> {
    IMap::empty().insert(
        if phase == 0 {
            0
        } else {
            4
        },
        if phase == 0 {
            1
        } else {
            5
        },
    ).insert(2, 3).insert(8, 9)
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 MoveEntry {
    fields {
        #[sharding(variable)] pub phase: int,
        #[sharding(imap)] pub entries: IMap<int,int>,
    }
    #[invariant] pub fn model(&self)->bool {
        (self.phase==0 || self.phase==1) && self.entries==entries_at(self.phase)
    }
    init! { initialize() { init phase=0; init entries=entries_at(0); } }
    transition! { move_entry() {
        require(pre.phase==0);
        remove entries -= [0=>1];
        have entries >= [2=>3];
        add entries += [4=>5];
        update phase=1;
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self) {}
    #[inductive(move_entry)] fn move_entry_inductive(pre:Self,post:Self) {
        assert(post.entries =~= entries_at(post.phase));
    }
} }

pub proof fn borrowed_observation() {
    let tracked full = MoveEntry::Protocol::initialize();
    let owner = MoveEntry::Fragment {
        phase: Some(ExclusiveRA::Exclusive(0)),
        entries: map_frag(IMap::empty().insert(0, 1)),
    };
    let shared = MoveEntry::Fragment {
        phase: None,
        entries: map_frag(IMap::empty().insert(2, 3).insert(8, 9)),
    };
    assert(IMap::empty().insert(0, 1).union_prefer_right(IMap::empty().insert(2, 3).insert(8, 9))
        =~= entries_at(0));
    map_join(
        IMap::<int, int>::empty().insert(0, 1),
        IMap::<int, int>::empty().insert(2, 3).insert(8, 9),
    );
    assert(MoveEntry::Fragment::op(owner, shared) == full.fragment());
    let tracked (owner, shared) = full.split(owner, shared);
    let tracked owner = MoveEntry::Protocol::move_entry_with_shared(owner, &shared);
    assert(owner.fragment().entries.at(0) is None);
    assert(owner.fragment().entries.at(4) == Some(ExclusiveRA::Exclusive(5)));
    assert(shared.fragment().entries.at(2) == Some(ExclusiveRA::Exclusive(3)));
    assert(shared.fragment().entries.at(8) == Some(ExclusiveRA::Exclusive(9)));
    assert(owner.loc() == shared.loc());
}

fn main() {
    proof {
        borrowed_observation();
    }
}

} // verus!
