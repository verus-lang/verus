// EXPECTED-ERROR: precondition not satisfied
#[path = "../logical_maps.rs"]
mod demo;
use vstd::prelude::*;
verus! {

proof fn replacement_must_use_the_same_key() {
    let tracked (owner, observer) = demo::allocate_entries();
    let tracked out = demo::Entries::Protocol::replace_with_shared(owner, &observer, 4int, 6int);
}

} // verus!
fn main() {}
