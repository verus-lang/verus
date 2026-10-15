// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_properties.rs"]
mod fixture;
use fixture::*;
use vstd::prelude::*;
verus! {

proof fn insufficient_count() {
    let tracked token = CountBounds::Protocol::initialize();
    // Nine owned count occurrences cannot supply the property's Have10 premise.
    let tracked impossible = CountBounds::Protocol::in_bounds(token);
}

fn main() {
}

} // verus!
