// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BorrowedWriter {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
        }
        init! { initialize() { init writer=true; init readers=Multiset::empty(); } }
        transition! { release() { remove writer -= true; } }
    }
}

pub proof fn cannot_remove_borrowed_writer() {
    let tracked all = BorrowedWriter::Protocol::initialize();
    let tracked empty = all.empty();
    let tracked invalid = BorrowedWriter::Protocol::release_with_shared(empty, &all);
}

} // verus!
fn main() {}
