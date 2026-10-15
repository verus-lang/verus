// EXPECTED-ERROR: precondition not satisfied
//! A reader owned by the frame cannot be consumed by an empty local owner.
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::tsm_collections::*;
use vstd::resource::tsm_multiset::*;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn consume_other_owner() {
    let local = Multiset::<int>::empty();
    let other = Multiset::singleton(10int);
    multiset_join(local, other);
    multiset_remove_frame(multiset_frag(local), multiset_frag(other), local.add(other), 10);
}

fn main() {
}

} // verus!
