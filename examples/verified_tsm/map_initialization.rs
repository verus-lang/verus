//! A map-only machine initializes and validates without trusted expansion.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    EmptyMap {
        fields { #[sharding(map)] pub entries: Map<int,int>, }
        init! { initialize() { init entries = Map::empty(); } }
    }
}

fn main() {
    proof {
        let tracked token = EmptyMap::Protocol::initialize();
        token.validate();
    }
}

} // verus!
