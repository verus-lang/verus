use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(change)]
    Names {
        fields {
            #[sharding(variable)] pub value: nat,
            #[sharding(storage_option)] pub storage: Option<nat>,
        }
        init! { initialize() {init value=0;init storage=None;} }
        transition! { change(observed:nat,initial:nat,physical_deposit:nat,next:nat,certificate:nat) {
            require observed==initial;
            update value=observed+physical_deposit+next+certificate;
        } }
    }
}

proof fn parameter_names() {
    let tracked token = Names::Protocol::initialize(IMap::tracked_empty());
    let tracked observation = Names::Protocol::change_observed(token, 1, 1, 2, 3, 4);
    assert(observation.token.fragment().value_value() == 10);
}

} // verus!
fn main() {}
