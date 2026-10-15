// EXPECTED-ERROR: precondition not satisfied
#[path = "../option_bindings.rs"]
mod definition;
use definition::{BoundOption, Payload};
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

pub proof fn cannot_remove_a_borrowed_bound_value() {
    let tracked all = BoundOption::Protocol::initialize(Payload::Number(7nat));
    let observed = BoundOption::Fragment {
        observed: Some(ExclusiveRA::Exclusive(None)),
        ..BoundOption::Fragment::unit()
    };
    let payload = BoundOption::Fragment {
        payload: Some(ExclusiveRA::Exclusive(Payload::Number(7nat))),
        ..BoundOption::Fragment::unit()
    };
    let tracked (observed, payload) = all.split(observed, payload);
    let tracked invalid = BoundOption::Protocol::remove_with_shared(observed, &payload);
}

} // verus!
fn main() {}
