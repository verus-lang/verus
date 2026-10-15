// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rewrite_observed_map() {
    let all = IMap::empty().insert(3int, 9int);
    let changed = IMap::empty().insert(3int, 10int);
    persistent_map_frag(all).op_unit();
    persistent_map_union_frame(
        persistent_map_frag(all),
        PersistentMapFragment::unit(),
        all,
        changed,
    );
}

fn main() {
}

} // verus!
