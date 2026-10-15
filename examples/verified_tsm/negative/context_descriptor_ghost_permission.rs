// EXPECTED-ERROR: expression has mode spec, expected mode proof
use vstd::cell::pcell::PointsTo;
use vstd::prelude::*;
use vstd::resource::tsm_context::Descriptor;

verus! {

proof fn cannot_mint_permission(
    tracked descriptor: Descriptor<PointsTo<u64>>,
) -> (tracked permission: PointsTo<u64>) {
    descriptor.value()
}

} // verus!
fn main() {}
