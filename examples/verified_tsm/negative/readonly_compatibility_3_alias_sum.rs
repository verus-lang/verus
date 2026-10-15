// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
#[path = "../readonly_compatibility_3.rs"]
mod model;
verus! {

proof fn alias_is_not_three_owned_occurrences() {
    let tracked token = Token::<model::Boolean>::alloc_state(true);
    token.facts_3(
        &token,
        &token,
        completes::<model::Boolean>(
            CountRA::op(token.fragment(), CountRA::op(token.fragment(), token.fragment())),
        ),
    );
}

fn main() {
}

} // verus!
