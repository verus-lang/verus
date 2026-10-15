// EXPECTED-ERROR: precondition not satisfied
#[path = "../guide_bool_operands.rs"]
mod demo;
use demo::BoolOperands;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

proof fn borrowed_presence_cannot_be_consumed() {
    let tracked token = BoolOperands::Protocol::initialize(true);
    let owner = BoolOperands::Fragment {
        auth: Some(ExclusiveRA::Exclusive(true)),
        ..BoolOperands::Fragment::unit()
    };
    let shared = BoolOperands::Fragment {
        present: vstd::resource::tsm::CountRA { count: 1 },
        ..BoolOperands::Fragment::unit()
    };
    let tracked (owner, shared) = token.split(owner, shared);
    let tracked _out = BoolOperands::Protocol::remove_optional_with_shared(owner, &shared, true);
}

} // verus!
fn main() {}
