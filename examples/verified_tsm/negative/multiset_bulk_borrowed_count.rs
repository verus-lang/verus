// EXPECTED-ERROR: precondition not satisfied
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::tsm_finite_multiset::*;
verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn rejected() {
    let local = Multiset::empty().insert(4int);
    let borrowed = Multiset::empty().insert(4int);
    let removed = Multiset::empty().insert(4int).insert(4int);
    finite_multiset_join(local, borrowed);
    finite_multiset_remove_many_frame(
        finite_multiset_frag(local),
        finite_multiset_frag(borrowed),
        local.add(borrowed),
        removed,
    );
}

} // verus!
fn main() {}
