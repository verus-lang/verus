// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_optional_operands.rs"]
mod demo;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
verus! {

proof fn removing_a_present_operand_consumes_owned_rights() {
    let tracked token = demo::OptionalOperands::Protocol::initialize(Some(7int));
    let owned = demo::OptionalOperands::Fragment {
        auth: Some(ExclusiveRA::Exclusive(Some(7int))),
        entry: None,
    };
    let shared = demo::OptionalOperands::Fragment {
        auth: None,
        entry: Some(ExclusiveRA::Exclusive(7int)),
    };
    let tracked (owned, shared) = token.split(owned, shared);
    let tracked output = demo::OptionalOperands::Protocol::remove_optional_with_shared(
        owned,
        &shared,
        Some(7int),
    );
}

} // verus!
fn main() {}
