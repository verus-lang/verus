//! Finite set ownership supports singleton and general operands.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
use vstd::set::*;

verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
SetPermissions {
    fields {
        #[sharding(variable)] pub active: Set<int>,
        #[sharding(set)] pub permissions: Set<int>,
        #[sharding(persistent_set)] pub observed: Set<int>,
    }
    #[invariant]
    pub fn permissions_match_active(self) -> bool { self.permissions == self.active }
    init! { initialize() {
        init active = Set::empty().insert(1int).insert(2int);
        init permissions = Set::empty().insert(1int).insert(2int);
        init observed = Set::empty();
    } }
    transition! { remove_many(removed: Set<int>) {
        remove permissions -= (removed);
        update active = pre.active.difference(removed);
    } }
    transition! { add_many(added: Set<int>) {
        require pre.active.disjoint(added);
        add permissions += (added);
        update active = pre.active.union(added);
    } }
    transition! { record(added: Set<int>) { add observed (union)= (added); } }
    transition! { observe(needed: Set<int>) { have observed >= (needed); } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(remove_many)] fn remove_many_inductive(pre: Self, post: Self, removed: Set<int>) {}
    #[inductive(add_many)] fn add_many_inductive(pre: Self, post: Self, added: Set<int>) {}
    #[inductive(record)] fn record_inductive(pre: Self, post: Self, added: Set<int>) {}
    #[inductive(observe)] fn observe_inductive(pre: Self, post: Self, needed: Set<int>) {}
});

pub proof fn allocate_without_permissions() -> (tracked tokens: (
    SetPermissions::Token,
    SetPermissions::Token,
))
    ensures
        tokens.0.loc() == tokens.1.loc(),
        tokens.0.fragment().active == Some(
            vstd::resource::exclusive::ExclusiveRA::Exclusive(
                Set::empty().insert(1int).insert(2int),
            ),
        ),
        tokens.0.fragment().permissions == SetFragment::<int>::unit(),
{
    broadcast use vstd::set::group_set_lemmas;

    let tracked token = SetPermissions::Protocol::initialize();
    let active = Set::empty().insert(1int).insert(2int);
    let owned = SetPermissions::Fragment {
        active: Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(active)),
        permissions: SetFragment::unit(),
        observed: PersistentSetFragment::unit(),
    };
    let shared = SetPermissions::Fragment {
        active: None,
        permissions: set_frag(active.to_iset()),
        observed: PersistentSetFragment::unit(),
    };
    Pointwise::extensionality(
        persistent_set_frag(Set::<int>::empty().to_iset()),
        PersistentSetFragment::unit(),
    );
    SetFragment::<int>::op_unit(set_frag(active.to_iset()));
    SetFragment::<int>::commutative(SetFragment::unit(), set_frag(active.to_iset()));
    PersistentSetFragment::<int>::op_unit(PersistentSetFragment::unit());
    token.split(owned, shared)
}

pub proof fn finite_set_history() {
    broadcast use vstd::set::group_set_lemmas;

    let tracked token = SetPermissions::Protocol::initialize();
    let tracked token = SetPermissions::Protocol::remove_many(token, Set::empty().insert(1int));
    let tracked token = SetPermissions::Protocol::add_many(token, Set::empty().insert(3int));
    let tracked token = SetPermissions::Protocol::remove_many(token, Set::empty());
    let tracked token = SetPermissions::Protocol::add_many(token, Set::empty());
    let tracked token = SetPermissions::Protocol::record(
        token,
        Set::empty().insert(5int).insert(6int),
    );
    let tracked token = SetPermissions::Protocol::record(token, Set::empty());
    assert(token.fragment().observed.at(5int) == Some(
        vstd::resource::agree::AgreementRA::Agree(()),
    ));
    let owned = token.fragment();
    let needed = Set::empty().insert(5int);
    SetPermissions::Fragment::op_unit(owned);
    assert forall|z: SetPermissions::Fragment, pre: SetPermissions::State|
        pre.invariant() && SetPermissions::Fragment::op(
            SetPermissions::Fragment::op(owned, SetPermissions::Fragment::unit()),
            z,
        ) == SetPermissions::Protocol::embed(pre) implies SetPermissions::State::observe_enabled(
        pre,
        needed,
    ) && SetPermissions::State::observe_owners_enabled(
        pre,
        owned,
        SetPermissions::Fragment::unit(),
        needed,
    ) by {
        persistent_set_have_many_frame(
            owned.observed,
            z.observed,
            pre.observed.to_iset(),
            needed.to_iset(),
        );
    }
    let tracked token = SetPermissions::Protocol::observe(token, Set::empty().insert(5int));
    assert(token.fragment().observed.at(5int) == Some(
        vstd::resource::agree::AgreementRA::Agree(()),
    ));
}

fn main() {
    proof {
        finite_set_history();
    }
}

} // verus!
