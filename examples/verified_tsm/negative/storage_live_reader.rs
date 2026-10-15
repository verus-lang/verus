// EXPECTED-ERROR: precondition not satisfied
#[path = "../storage.rs"]
mod protocol;
use protocol::{control, stored, RefCounter};
use vstd::cell::pcell_maybe_uninit::PointsTo;
use vstd::prelude::*;
use vstd::resource::tsm_storage::StorageToken;

verus! {

proof fn cannot_withdraw_with_a_reader(
    tracked token: StorageToken<RefCounter>,
    permission: PointsTo<u64>,
)
    requires
        token.fragment() == control(Some((1, permission))),
{
    let tracked _invalid = token.exchange(IMap::tracked_empty(), control(None), stored(permission));
}

} // verus!
fn main() {}
