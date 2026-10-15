//! Finite reader fragments preserve frame counts and accept recursive values.
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm_finite_multiset::*;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn finite_reader_frames() {
    let local = Multiset::singleton(10int);
    let other = Multiset::singleton(10int).insert(20int);
    let whole = local.add(other);
    let owned = finite_multiset_frag(local);
    let frame = finite_multiset_frag(other);
    finite_multiset_join(local, other);
    finite_multiset_add_frame(owned, frame, whole, 10);
    finite_multiset_remove_frame(owned.insert(10), frame, whole.insert(10), 10);
    FiniteMultisetRA::extensionality(owned.insert(10).remove(10), owned);
    finite_multiset_remove_frame(owned, frame, whole, 10);
    assert(FiniteMultisetRA::op(owned.remove(10), frame).at(10).count == 1);
    assert(FiniteMultisetRA::op(owned.remove(10), frame).at(20).count == 1);
}

pub enum ReaderTree {
    Leaf,
    Branch(FiniteMultisetRA<ReaderTree>),
}

fn main() {
    let _empty = ReaderTree::Leaf;
}

} // verus!
