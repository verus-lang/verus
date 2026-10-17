// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BorrowedVariable {
        fields { #[sharding(variable)] pub value:int, }
        init! { initialize() { init value=0; } }
        transition! { increment() { update value=pre.value+1; } }
    }
}

pub proof fn borrowed_variable_is_not_owned() {
    use vstd::resource::exclusive::ExclusiveRA;
    let tracked all = BorrowedVariable::Protocol::initialize();
    let tracked (owner, reader) = all.split(
        BorrowedVariable::Fragment { value: None },
        BorrowedVariable::Fragment { value: Some(ExclusiveRA::Exclusive(0int)) },
    );
    let tracked invalid = BorrowedVariable::Protocol::increment_with_shared(owner, &reader);
}

} // verus!
fn main() {}
