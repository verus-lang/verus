//! Sequential map Have sees the current local fragment in both branches.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;

verus! {

pub open spec fn rows(phase: int) -> IMap<int, int> {
    IMap::empty().insert(
        0,
        if phase == 1 {
            11
        } else {
            10
        },
    ).insert(
        1,
        if phase == 2 {
            21
        } else {
            20
        },
    ).insert(2, 30)
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 OrderedEntries {
    fields {
        #[sharding(variable)] pub phase: int,
        #[sharding(imap)] pub entries: IMap<int,int>,
    }
    #[invariant] pub fn model(&self)->bool {
        0 <= self.phase <= 2 && self.entries == rows(self.phase)
    }
    init! { initialize() { init phase = 0; init entries = rows(0); } }
    transition! { advance(branch: bool) {
        require(pre.phase == 0);
        if branch {
            remove entries -= [0 => let old];
            have entries >= [1 => 20];
            add entries += [0 => old + 1];
            update phase = 1;
        } else {
            remove entries -= [1 => let other];
            have entries >= [0 => 10];
            add entries += [1 => other + 1];
            update phase = 2;
        }
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self) {}
    #[inductive(advance)] fn advance_inductive(pre:Self,post:Self,branch:bool) {
        assert(post.entries =~= rows(post.phase));
    }
} }

pub proof fn untouched_owner(branch: bool) {
    let tracked full = OrderedEntries::Protocol::initialize();
    let owner = OrderedEntries::Fragment {
        phase: Some(ExclusiveRA::Exclusive(0)),
        entries: map_frag(rows(0).remove(2)),
    };
    let outside = OrderedEntries::Fragment {
        phase: None,
        entries: map_frag(IMap::empty().insert(2, 30)),
    };
    assert(full.fragment().phase == Some(ExclusiveRA::Exclusive(0)));
    assert(full.fragment().entries == map_frag(rows(0)));
    assert(rows(0).remove(2).union_prefer_right(IMap::empty().insert(2, 30)) =~= rows(0));
    map_join(rows(0).remove(2), IMap::empty().insert(2, 30));
    assert(OrderedEntries::Fragment::op(owner, outside) == full.fragment());
    let tracked (owner, outside) = full.split(owner, outside);
    let ghost old = owner.fragment();
    let tracked owner = OrderedEntries::Protocol::advance(owner, branch);
    assert(owner.fragment().entries.at(2) is None);
    assert(outside.fragment().entries.at(2) == Some(ExclusiveRA::Exclusive(30)));
    assert(owner.loc() == outside.loc());
}

fn main() {
    proof {
        untouched_owner(true);
        untouched_owner(false);
    }
}

} // verus!
