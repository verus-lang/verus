// EXPECTED-ERROR: precondition not satisfied
#[path = "../test_option_empty_operands.rs"]
mod fixture;
use fixture::*;
use vstd::prelude::*;
verus! {

proof fn wrong_guard() {
    let tracked mut base = IMap::tracked_empty();
    let tracked actual_permission = 9int;
    base.tracked_insert(0int, actual_permission);
    let tracked token = SafeY::Protocol::initialize(base, Some(7int), Some(9int));
    let tracked guard = SafeY::Protocol::retained_permission(&token, 10int);
}

fn main() {
}

} // verus!
