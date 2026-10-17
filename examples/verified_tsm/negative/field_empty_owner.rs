// EXPECTED-ERROR: assertion failed
use vstd::prelude::*;
#[path = "../counting_to_2.rs"]
mod demo;
verus! {

proof fn missing_field_is_not_owned() {
    let tracked all = demo::X::Protocol::initialize();
    let tracked (only_a, remaining) = demo::X::Protocol::take_inc_a(all);
    assert(only_a.fragment().owns_counter());
}

} // verus!
fn main() {}
