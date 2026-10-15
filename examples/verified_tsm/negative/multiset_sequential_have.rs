// EXPECTED-ERROR: precondition not satisfied
//! After consuming the only owned reader, Have cannot use the consumed rights.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    SequentialReaders {
        fields { #[sharding(multiset)] pub readers:Multiset<int>, }
        init! { initialize() { init readers=Multiset::singleton(1int); } }
        transition! { consumed_then_have() { remove readers -= {1int}; have readers >= {1int}; } }
    }
}

proof fn consumed_rights_cannot_be_observed() {
    let tracked token = SequentialReaders::Protocol::initialize();
    let tracked token = SequentialReaders::Protocol::consumed_then_have(token);
}

} // verus!
fn main() {}
