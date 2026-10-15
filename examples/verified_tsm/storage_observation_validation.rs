use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::{completes, Machine};
use vstd::resource::tsm_storage::{StorageMachine, StorageToken};
verus! {

proof fn validate_real_pair<M: StorageMachine>(
    tracked mut owned: StorageToken<M>,
    tracked other: &StorageToken<M>,
) -> (tracked result: StorageToken<M>)
    requires
        owned.loc() == other.loc(),
    ensures
        result.loc() == owned.loc(),
        result.fragment() == owned.fragment(),
        completes::<M>(M::Fragment::op(result.fragment(), other.fragment())),
{
    let tracked observation = other.observe();
    owned.validate_with_observation(&observation);
    owned
}

proof fn validate_aliased_observers<M: StorageMachine>(
    tracked mut owned: StorageToken<M>,
    tracked other: &StorageToken<M>,
) -> (tracked result: StorageToken<M>)
    requires
        owned.loc() == other.loc(),
    ensures
        result.loc() == owned.loc(),
        result.fragment() == owned.fragment(),
{
    let tracked observation = other.observe();
    let tracked joined = observation.join(&observation);
    owned.validate_with_observation(&joined);
    assert(completes::<M>(M::Fragment::op(owned.fragment(), joined.fragment())));
    owned
}

fn main() {
}

} // verus!
