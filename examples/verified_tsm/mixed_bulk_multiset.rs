//! Bulk multiset operands work beside boolean fields.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::pcm::PCM;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BulkReaders {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
        }
        init! { initialize() { init writer=false; init readers=Multiset::singleton(7nat); } }
        transition! { release(values:Multiset<nat>) { remove readers -= (values); } }
    }
}

proof fn removing_the_whole_owned_bag() {
    let tracked token = BulkReaders::Protocol::initialize();
    let tracked token = BulkReaders::Protocol::release(token, Multiset::singleton(7nat));
    assert(token.fragment().readers.values =~= Multiset::<nat>::empty());
    assert(token.fragment().writer.count == 0);
}

fn main() {
    proof {
        removing_the_whole_owned_bag();
    }
}

} // verus!
