// EXPECTED-ERROR: precondition not satisfied
#[path = "../persistent_bool_algebra.rs"]
mod model;
use vstd::prelude::*;
use vstd::resource::tsm::Token;
use vstd::resource::tsm_persistent::PersistentCountRA;
verus! {

proof fn rejected() {
    let tracked _token = Token::<model::BooleanKnowledge>::alloc(PersistentCountRA { count: 2 });
}

} // verus!
fn main() {}
