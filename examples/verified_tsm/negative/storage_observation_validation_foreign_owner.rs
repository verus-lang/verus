use vstd::prelude::*;
use vstd::resource::tsm_storage::{StorageMachine, StorageToken};
verus! {

proof fn foreign_owner<M: StorageMachine>(
    tracked mut owned: StorageToken<M>,
    tracked other: &StorageToken<M>,
) {
    let tracked observation = other.observe();
    owned.validate_with_observation(&observation);
}

fn main() {
}

} // verus!
