// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    SequentialReaders {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
        }
        init! { initialize() { init writer=false; init readers=Multiset::singleton(7nat); } }
        transition! { release() {
            remove readers -= {7nat};
            have readers >= {7nat};
        } }
    }
}

proof fn a_removed_reader_cannot_satisfy_a_later_have() {
    let tracked token = SequentialReaders::Protocol::initialize();
    let tracked token = SequentialReaders::Protocol::release(token);
}

} // verus!
fn main() {}
