// EXPECTED-ERROR: precondition not satisfied
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::prelude::*;
use vstd::resource::tsm_helpers::singleton_map;
#[path = "../ref_cell.rs"]
mod demo;
verus! {

fn wrong_permission() {
    let (pcell, Tracked(permission)) = cell::PCell::new(7u64);
    let (_other, Tracked(other_permission)) = cell::PCell::new(99u64);
    let tracked all = demo::RefCounter::Protocol::<u64>::initialize_empty(
        IMap::tracked_empty(),
        pcell.id(),
    );
    let ghost value = permission;
    let tracked deposit = singleton_map(0int, other_permission);
    let tracked _bad = demo::RefCounter::Protocol::<u64>::do_deposit_observed(all, deposit, value);
}

} // verus!
fn main() {}
