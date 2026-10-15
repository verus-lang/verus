// EXPECTED-ERROR: precondition not satisfied
//! The addition must be disjoint from the full state, including hidden owners.
use vstd::prelude::*;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn add_hidden_member() {
    let hidden = ISet::empty().insert(3int);
    set_add_many_frame(SetFragment::unit(), set_frag(hidden), hidden, hidden);
}

fn main() {
}

} // verus!
