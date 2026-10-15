// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
use vstd::resource::tsm_storage::StorageToken;
#[path = "../storage_validation.rs"]
mod validation;

verus! {

proof fn unrelated_tokens(
    tracked mut owned: StorageToken<validation::Bounded>,
    tracked shared: &StorageToken<validation::Bounded>,
)
    requires
        owned.loc() != shared.loc(),
{
    owned.validate_2(shared);
}

fn main() {
}

} // verus!
