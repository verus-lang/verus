//! Option element patterns reveal owned or borrowed values through checked proofs.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

pub enum Payload {
    Number(nat),
    Empty,
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BoundOption {
        fields {
            #[sharding(option)] pub payload:Option<Payload>,
            #[sharding(variable)] pub observed:Option<nat>,
        }
        init! { initialize(value:Payload) {
            init payload=Some(value);
            init observed=None;
        } }
        transition! { observe() {
            have payload >= Some(let Payload::Number(value));
            update observed=Some(value);
        } }
        transition! { remove() {
            remove payload -= Some(let Payload::Number(value));
            update observed=Some(value);
        } }
    }
}

pub proof fn borrowed_value_and_owned_removal() {
    let tracked all = BoundOption::Protocol::initialize(Payload::Number(7nat));
    let observed = BoundOption::Fragment {
        observed: Some(ExclusiveRA::Exclusive(None)),
        ..BoundOption::Fragment::unit()
    };
    let payload = BoundOption::Fragment {
        payload: Some(ExclusiveRA::Exclusive(Payload::Number(7nat))),
        ..BoundOption::Fragment::unit()
    };
    let tracked (observed, payload) = all.split(observed, payload);
    let tracked observed = BoundOption::Protocol::observe_with_shared(observed, &payload);
    assert(observed.fragment().observed->Some_0->Exclusive_0 == Some(7nat));
    assert(payload.fragment().payload == Some(ExclusiveRA::Exclusive(Payload::Number(7nat))));
    let tracked all = observed.join(payload);
    let tracked removed = BoundOption::Protocol::remove(all);
    assert(removed.fragment().payload is None);
    assert(removed.fragment().observed->Some_0->Exclusive_0 == Some(7nat));
}

} // verus!
fn main() {}
