//! Infinite set carriers retain exclusive members and persistent observations.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;

verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
InfinitePermissions {
    fields {
        #[sharding(variable)] pub active: ISet<int>,
        #[sharding(iset)] pub permissions: ISet<int>,
        #[sharding(persistent_iset)] pub observed: ISet<int>,
    }
    #[invariant]
    pub fn permissions_match_active(self) -> bool { self.permissions == self.active }
    init! { initialize() {
        init active = ISet::full();
        init permissions = ISet::full();
        init observed = ISet::empty();
    } }
    transition! { remove_one(value: int) {
        remove permissions -= set {value};
        update active = pre.active.remove(value);
    } }
    transition! { record_one(value: int) { add observed (union)= set {value}; } }
    transition! { record(added: ISet<int>) { add observed (union)= (added); } }
    readonly! { observe(needed: ISet<int>) { have observed >= (needed); } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(remove_one)] fn remove_one_inductive(pre: Self, post: Self, value: int) {}
    #[inductive(record_one)] fn record_one_inductive(pre: Self, post: Self, value: int) {}
    #[inductive(record)] fn record_inductive(pre: Self, post: Self, added: ISet<int>) {}
});

pub proof fn infinite_set_history() {
    let tracked token = InfinitePermissions::Protocol::initialize();
    let tracked token = InfinitePermissions::Protocol::remove_one(token, 1int);
    let tracked token = InfinitePermissions::Protocol::record_one(token, 7int);
    let tracked token = InfinitePermissions::Protocol::record(token, ISet::empty());
    let tracked token = InfinitePermissions::Protocol::record(token, ISet::full());
    let owned = token.fragment();
    assert forall|key: int| #[trigger]
        owned.observed.at(key) == Some(vstd::resource::agree::AgreementRA::Agree(())) by {};
    InfinitePermissions::Fragment::op_unit(owned);
    assert forall|z: InfinitePermissions::Fragment, pre: InfinitePermissions::State|
        pre.invariant() && InfinitePermissions::Fragment::op(
            InfinitePermissions::Fragment::op(owned, InfinitePermissions::Fragment::unit()),
            z,
        ) == InfinitePermissions::Protocol::embed(
            pre,
        ) implies InfinitePermissions::State::observe_enabled(pre, ISet::full())
        && InfinitePermissions::State::observe_owners_enabled(
        pre,
        owned,
        InfinitePermissions::Fragment::unit(),
        ISet::full(),
    ) by {
        persistent_set_have_many_frame(owned.observed, z.observed, pre.observed, ISet::full());
    }
    let tracked token = InfinitePermissions::Protocol::observe(token, ISet::full());
    let tracked token = InfinitePermissions::Protocol::observe(token, ISet::empty());
}

fn main() {
    proof {
        infinite_set_history();
    }
}

} // verus!
