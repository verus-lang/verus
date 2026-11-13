use super::super::prelude::*;

use std::process::{ExitCode, Termination};

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExExitCode(ExitCode);

#[verifier::external_trait_specification]
pub trait ExTermination {
    type ExternalTraitSpecificationFor: Termination;

    fn report(self) -> ExitCode;
}

} // verus!
