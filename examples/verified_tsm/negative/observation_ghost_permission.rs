// EXPECTED-ERROR: expression has mode spec, expected mode proof
use vstd::cell::pcell_maybe_uninit as cell;
use vstd::prelude::*;
#[path = "../ref_cell.rs"]
mod demo;
verus! {

proof fn forbidden_ghost_permission(
    tracked observation: demo::RefCounter::TransitionObservation<u64>,
) -> (tracked permission: cell::PointsTo<u64>)
    requires
        observation.before.storage is Some,
{
    observation.before.storage->Some_0
}

} // verus!
fn main() {}
