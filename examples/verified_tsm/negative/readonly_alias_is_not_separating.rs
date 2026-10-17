// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
#[path = "../readonly_compatibility.rs"]
mod model;

verus! {

proof fn cannot_count_an_alias_twice() {
    let tracked token = Token::<model::Boolean>::alloc_state(true);
    token.facts_2(
        &token,
        completes::<model::Boolean>(CountRA::op(token.fragment(), token.fragment())),
    );
}

fn main() {
}

} // verus!
