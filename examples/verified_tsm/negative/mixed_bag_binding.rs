// EXPECTED-ERROR: A let-pattern binding is not supported here
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BoundReaders {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(multiset)] pub readers:Multiset<nat>,
        }
        init! { initialize() { init writer=false; init readers=Multiset::singleton(7nat); } }
        transition! { observe() { have readers >= {let value}; } }
    }
}

} // verus!
fn main() {}
