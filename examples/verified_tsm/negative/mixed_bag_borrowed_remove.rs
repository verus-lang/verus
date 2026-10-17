// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BorrowedReader {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
        }
        init! { initialize() { init writer=false; init readers=Multiset::singleton(7nat); } }
        transition! { release() { remove readers -= {7nat}; } }
    }
}

pub proof fn cannot_remove_borrowed_reader() {
    let tracked all = BorrowedReader::Protocol::initialize();
    let tracked empty = all.empty();
    let tracked invalid = BorrowedReader::Protocol::release_with_shared(empty, &all);
}

} // verus!
fn main() {}
