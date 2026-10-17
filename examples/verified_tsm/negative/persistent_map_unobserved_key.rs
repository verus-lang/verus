// EXPECTED-ERROR: precondition not satisfied
#[path = "../persistent_map_properties.rs"]
mod definition;
use definition::PersistentMaps;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

pub proof fn cannot_choose_an_unobserved_key() {
    let tracked all = PersistentMaps::Protocol::initialize();
    let observations = PersistentMaps::Fragment {
        finite: persistent_map_frag(IMap::empty().insert(0nat, 7int)),
        infinite: persistent_map_frag(IMap::empty().insert(0nat, 7int)),
        ..PersistentMaps::Fragment::unit()
    };
    let selection = PersistentMaps::Fragment {
        selected: Some(ExclusiveRA::Exclusive(0nat)),
        ..PersistentMaps::Fragment::unit()
    };
    observations.finite.op_unit();
    observations.infinite.op_unit();
    assert(Map::<nat, int>::empty().insert(0nat, 7int).to_imap() =~= IMap::empty().insert(
        0nat,
        7int,
    ));
    Pointwise::extensionality(all.fragment().finite, observations.finite);
    let tracked (observations, _selection) = all.split(observations, selection);
    let tracked invalid = PersistentMaps::Protocol::observe_selected(observations);
}

} // verus!
fn main() {}
