//! Mathematical reader-count operations preserve another owner's readers,
//! including another occurrence of the same permission value.
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::CountRA;
use vstd::resource::tsm_collections::*;
use vstd::resource::tsm_multiset::*;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn reader_frames() {
    let local = Multiset::singleton(10int);
    let other = Multiset::singleton(10int).insert(20int);
    let whole = local.add(other);
    let owned = multiset_frag(local);
    let frame = multiset_frag(other);
    multiset_join(local, other);
    multiset_owned_frame(owned, frame, whole, 10);
    assert(whole.count(10) == 2);

    multiset_add_frame(owned, frame, whole, 10);
    let duplicated = replace_at(owned, 10, CountRA { count: 2 });
    assert(MultisetFragment::op(duplicated, frame) == multiset_frag(whole.insert(10)));

    multiset_remove_frame(duplicated, frame, whole.insert(10), 10);
    let once = replace_at(duplicated, 10, CountRA { count: 1 });
    Pointwise::extensionality(once, owned);
    multiset_remove_frame(once, frame, whole, 10);
    let empty = replace_at(once, 10, CountRA { count: 0 });
    assert(MultisetFragment::op(empty, frame).at(10).count == 1);
    assert(MultisetFragment::op(empty, frame).at(20).count == 1);
    assert(frame.at(10).count == 1);
    assert(frame.at(20).count == 1);
}

fn main() {
}

} // verus!
