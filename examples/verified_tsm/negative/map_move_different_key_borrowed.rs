// EXPECTED-ERROR: precondition not satisfied
#[path = "../map_move_different_key.rs"]
mod fixture;
use fixture::*;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::tsm_collections::*;
verus! {

proof fn borrowed_consumption() {
    let tracked full = MoveEntry::Protocol::initialize();
    let owner = MoveEntry::Fragment {
        phase: Some(ExclusiveRA::Exclusive(0)),
        entries: map_frag(IMap::<int, int>::empty()),
    };
    let shared = MoveEntry::Fragment { phase: None, entries: map_frag(entries_at(0)) };
    map_join(IMap::<int, int>::empty(), entries_at(0));
    assert(IMap::<int, int>::empty().union_prefer_right(entries_at(0)) =~= entries_at(0));
    assert(MoveEntry::Fragment::op(owner, shared) == full.fragment());
    let tracked (owner, shared) = full.split(owner, shared);
    let tracked owner = MoveEntry::Protocol::move_entry_with_shared(owner, &shared);
}

fn main() {
}

} // verus!
