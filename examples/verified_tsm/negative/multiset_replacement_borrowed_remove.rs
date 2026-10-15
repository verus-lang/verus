// EXPECTED-ERROR: precondition not satisfied
#[path = "../multiset_replacement.rs"]
mod fixture;
use fixture::*;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn borrowed_remove() {
    let tracked token = BagReplacement::Protocol::initialize();
    assert(Multiset::empty().insert(11int).add(Multiset::empty().insert(10int).insert(99int))
        =~= token.fragment().bag.values);
    let tracked (owned, borrowed) = token.split(
        fragment(Multiset::empty().insert(11int)),
        fragment(Multiset::empty().insert(10int).insert(99int)),
    );
    let tracked token = BagReplacement::Protocol::replace_with_shared(owned, &borrowed);
}

fn main() {
}

} // verus!
