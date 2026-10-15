// EXPECTED-ERROR: precondition not satisfied
//! An entire removed set must be locally owned, including every member.
use vstd::prelude::*;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn remove_borrowed_set() {
    let all = ISet::new(|v: int| v >= 0);
    set_remove_many_frame(SetFragment::unit(), set_frag(all), all, all);
}

fn main() {
}

} // verus!
