// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn add_hidden_key() {
    let all = IMap::empty().insert(3int, 9int);
    map_frag(all).op_unit();
    MapFragment::commutative(MapFragment::unit(), map_frag(all));
    map_add_many_frame(MapFragment::unit(), map_frag(all), all, all);
}

fn main() {
}

} // verus!
