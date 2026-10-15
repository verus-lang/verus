use vstd::prelude::*;
use vstd::resource::tsm_storage::{StorageMachine, StorageToken};
verus! {

proof fn live_owner_borrow<M: StorageMachine>(tracked mut owned: StorageToken<M>) {
    let tracked observation = owned.observe();
    owned.validate_with_observation(&observation);
    observation.validate();
}

fn main() {
}

} // verus!
