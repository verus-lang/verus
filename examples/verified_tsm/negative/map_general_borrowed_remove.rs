// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_map_operands.rs"]
mod demo;
use demo::MapOperands;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn borrowed_entries_cannot_be_consumed() {
    let pair = Map::empty().insert(1nat, 10int).insert(2nat, 20int);
    let tracked full = MapOperands::Protocol::initialize(pair);
    let owner = MapOperands::Fragment {
        auth: Some(ExclusiveRA::Exclusive(pair)),
        entries: MapFragment::unit(),
    };
    let shared = MapOperands::Fragment { auth: None, entries: map_frag(pair.to_imap()) };
    assert(full.fragment().auth == Some(ExclusiveRA::Exclusive(pair)));
    assert(full.fragment().entries == map_frag(pair.to_imap()));
    MapFragment::op_unit(shared.entries);
    MapFragment::commutative(owner.entries, shared.entries);
    assert(MapOperands::Fragment::op(owner, shared) == full.fragment());
    let tracked (owner, shared) = full.split(owner, shared);
    let tracked _out = MapOperands::Protocol::remove_many_with_shared(owner, &shared, pair);
}

} // verus!
fn main() {}
