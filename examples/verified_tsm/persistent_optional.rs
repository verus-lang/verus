//! A persistent optional observation accepts empty and agreeing operands.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm_collections::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
PersistentOptional {
    fields {
        #[sharding(variable)] pub auth: Option<int>,
        #[sharding(persistent_option)] pub observed: Option<int>,
    }
    #[invariant] pub fn agrees(self) -> bool { self.auth == self.observed }
    #[invariant] pub fn stable_choice(self) -> bool {
        self.observed is Some ==> self.observed->Some_0 == 7int
    }
    init! { initialize() { init auth = None; init observed = None; } }
    transition! { record(value: Option<int>) {
        require value is None || value->Some_0 == 7int;
        require pre.auth is None || value is None || pre.auth == value;
        update auth = if value is Some { value } else { pre.auth };
        add observed (union)= (value);
    } }
    readonly! { observe(value: Option<int>) { have observed >= (value); } }
    readonly! { observe_bound() {
        have observed >= Some(let selected);
        assert(selected == 7int);
    } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(record)] fn record_inductive(pre: Self, post: Self, value: Option<int>) {}
});

pub proof fn optional_persistence_history() {
    let tracked token = PersistentOptional::Protocol::initialize();
    let tracked token = PersistentOptional::Protocol::observe(token, None);
    let tracked token = PersistentOptional::Protocol::record(token, None);
    let tracked token = PersistentOptional::Protocol::record(token, Some(7int));
    let tracked token = PersistentOptional::Protocol::observe(token, Some(7int));
    let tracked token = PersistentOptional::Protocol::observe_bound(token);
    let tracked token = PersistentOptional::Protocol::record(token, Some(7int));
    let tracked token = PersistentOptional::Protocol::record(token, None);
    let tracked token = PersistentOptional::Protocol::observe(token, None);
    assert(token.fragment().observed == Some(vstd::resource::agree::AgreementRA::Agree(7int)));
}

pub proof fn duplicating_an_optional_observation() {
    let tracked token = PersistentOptional::Protocol::initialize();
    let tracked token = PersistentOptional::Protocol::record(token, Some(7int));
    let auth = PersistentOptional::Fragment { auth: token.fragment().auth, observed: None };
    let observation = PersistentOptional::Fragment {
        auth: None,
        observed: Some(vstd::resource::agree::AgreementRA::Agree(7int)),
    };
    let tracked (auth, observation) = token.split(auth, observation);
    persistent_option_idempotent(Some(7int));
    assert(PersistentOptional::Fragment::op(observation.fragment(), observation.fragment())
        == observation.fragment());
    let tracked copied = observation.duplicate();
    let tracked copied = PersistentOptional::Protocol::observe(copied, Some(7int));
    assert(copied.loc() == observation.loc());
}

fn main() {
    proof {
        optional_persistence_history();
        duplicating_an_optional_observation();
    }
}

} // verus!
