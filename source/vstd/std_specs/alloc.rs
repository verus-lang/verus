use super::super::prelude::*;

verus! {

// this is a bit of a hack; verus treats Global specially already,
// but putting this here helps Verus pick up all the trait impls for Global
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGlobal(alloc::alloc::Global);

} // verus!
