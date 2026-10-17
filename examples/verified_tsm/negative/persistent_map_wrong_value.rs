// EXPECTED-ERROR: precondition not satisfied
#[path = "../persistent_map_properties.rs"]
mod definition;
use definition::PersistentMaps;
use vstd::prelude::*;
verus! {

pub proof fn cannot_observe_another_value() {
    let tracked all = PersistentMaps::Protocol::initialize();
    let tracked invalid = PersistentMaps::Protocol::compare(all, 0nat, 8int, 0nat, 7int);
}

} // verus!
fn main() {}
