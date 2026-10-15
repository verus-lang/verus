// EXPECTED-ERROR: precondition not satisfied
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::tsm_finite_multiset::*;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn consume_other_owner() {
    let local = Multiset::<int>::empty();
    let other = Multiset::singleton(10int);
    finite_multiset_join(local, other);
    finite_multiset_remove_frame(
        finite_multiset_frag(local),
        finite_multiset_frag(other),
        local.add(other),
        10,
    );
}

fn main() {
}

} // verus!
