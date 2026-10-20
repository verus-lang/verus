// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_properties.rs"]
mod fixture;
use fixture::*;
use vstd::cell::pcell::PCell;
use vstd::prelude::*;
verus! {

fn wrong_permission_guard() {
    let (_first, Tracked(permission)) = PCell::new(42u64);
    let (_second, Tracked(other_permission)) = PCell::new(99u64);
    let ghost p = permission;
    let ghost wrong = other_permission;
    let tracked token = DepositedCell::Protocol::initialize(IMap::tracked_empty(), p);
    let tracked deposit = DepositedCell::__pack_perm(Some(permission));
    let tracked token = DepositedCell::Protocol::deposit_local(token, deposit, p);
    // The deposited Bool does not authorize an arbitrary permission argument.
    let tracked guard = DepositedCell::Protocol::get_perm_ref(&token, wrong);
}

fn main() {
}

} // verus!
