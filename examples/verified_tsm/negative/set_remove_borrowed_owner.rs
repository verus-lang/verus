// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;
verus! {

proof fn rejected() {
    let full = ISet::empty().insert(0int);
    let owned = SetFragment::<int>::unit();
    let frame = set_frag(full);
    SetFragment::<int>::op_unit(frame);
    SetFragment::<int>::commutative(owned, frame);
    set_remove_frame(owned, frame, full, 0int);
}

} // verus!
fn main() {}
