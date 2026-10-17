// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn remove_borrowed_map() {
    let all = IMap::new(|key: int| key >= 0, |key: int| key);
    map_frag(all).op_unit();
    MapFragment::commutative(MapFragment::unit(), map_frag(all));
    map_remove_many_frame(MapFragment::unit(), map_frag(all), all, all);
}

fn main() {
}

} // verus!
