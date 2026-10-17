// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_storage::StorageToken;
#[path = "../readonly_compatibility.rs"]
mod model;

verus! {

proof fn cannot_claim_incompatible_observations() {
    let tracked all = StorageToken::<model::Pair>::alloc_state((true, true), IMap::tracked_empty());
    let tracked (left, right) = all.split(model::left_fragment(true), model::right_fragment(true));
    left.facts_2(
        &right,
        left.fragment().left->Some_0->Exclusive_0 != right.fragment().right->Some_0->Exclusive_0,
    );
}

fn main() {
}

} // verus!
