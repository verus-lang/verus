// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_storage_optional_operands.rs"]
mod fixture;
use fixture::*;
use vstd::cell::PCell;
use vstd::prelude::*;
verus! {

fn wrong_empty_transfer() {
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let tracked owner = OptionalStorage::Protocol::initialize(
        IMap::tracked_empty(),
        cell.id(),
        None,
    );
    let tracked deposited = OptionalStorage::__pack_stored(Some(permission));
    let tracked owner = OptionalStorage::Protocol::deposit_optional(owner, deposited, None);
}

fn main() {
}

} // verus!
