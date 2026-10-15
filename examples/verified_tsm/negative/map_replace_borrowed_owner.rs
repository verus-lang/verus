// EXPECTED-ERROR: precondition not satisfied
#[path = "../logical_maps.rs"]
mod demo;
use vstd::prelude::*;
verus! {

proof fn borrowed_owner_cannot_replace() {
    let tracked (_, observer) = demo::allocate_entries();
    let tracked empty = observer.empty();
    let tracked out = demo::Entries::Protocol::replace_with_shared(empty, &observer, 9int, 9int);
}

} // verus!
fn main() {}
