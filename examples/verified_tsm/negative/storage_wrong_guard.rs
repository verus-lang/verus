// EXPECTED-ERROR: precondition not satisfied
#[path = "../storage.rs"]
mod protocol;
use protocol::{reader, stored, RefCounter};
use vstd::cell::pcell_maybe_uninit::PointsTo;
use vstd::prelude::*;
use vstd::resource::tsm_storage::StorageToken;

verus! {

proof fn cannot_guard_another_permission(
    tracked token: &StorageToken<RefCounter>,
    held: PointsTo<u64>,
    other: PointsTo<u64>,
)
    requires
        token.fragment() == reader(held),
        held != other,
{
    let tracked _invalid = token.guard(stored(other));
}

} // verus!
fn main() {}
