// EXPECTED-ERROR: precondition not satisfied
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::prelude::*;
use vstd::resource::tsm_helpers::singleton_map;
#[path = "../ref_cell.rs"]
mod demo;
verus! {

fn borrowed_is_not_owned() {
    let (pcell, Tracked(permission)) = cell::PCell::new(7u64);
    let tracked all = demo::RefCounter::Protocol::<u64>::initialize_empty(
        IMap::tracked_empty(),
        pcell.id(),
    );
    let tracked (writer, flag) = demo::RefCounter::Protocol::<u64>::take_writer(all);
    let ghost value = permission;
    let tracked deposit = singleton_map(0int, permission);
    let tracked _bad = demo::RefCounter::Protocol::<u64>::do_deposit_local_with_shared(
        flag,
        &writer,
        deposit,
        value,
    );
}

} // verus!
fn main() {}
