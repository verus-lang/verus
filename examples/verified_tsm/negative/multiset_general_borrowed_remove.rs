// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_multiset_operands.rs"]
mod demo;
use demo::BagOperands;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

broadcast use vstd::multiset::group_multiset_axioms;

proof fn shared_multiplicity_cannot_be_consumed() {
    let one = Multiset::empty().insert(7int);
    let two = one.add(one);
    let tracked token = BagOperands::Protocol::initialize(two);
    let fragment = BagOperands::Fragment {
        values: vstd::resource::tsm_finite_multiset::finite_multiset_frag(one),
    };
    let tracked (owner, shared) = token.split(fragment, fragment);
    let tracked _out = BagOperands::Protocol::remove_many_with_shared(owner, &shared, two);
}

} // verus!
fn main() {}
