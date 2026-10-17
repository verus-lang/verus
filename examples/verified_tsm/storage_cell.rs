//! A PCell client deposits its real PointsTo permission in a generated protocol.
//! Borrowed guards remain usable while an independent fragment changes. Owned
//! withdrawal permits PCell::replace, followed by redeposit and another borrow.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::pcell::{PCell, PointsTo};
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    StoredCell {
        fields {
            #[sharding(variable)] pub owner: Option<PointsTo<u64>>,
            #[sharding(variable)] pub marker: nat,
            #[sharding(storage_option)] pub slot: Option<PointsTo<u64>>,
        }
        #[invariant] pub fn stored_matches_owner(&self)->bool { self.slot == self.owner }
        init! { initialize() { init owner = None; init marker = 0; init slot = None; } }
        transition! { deposit(value: PointsTo<u64>) {
            require pre.owner is None;
            deposit slot += Some(value);
            update owner = Some(value);
        } }
        transition! { withdraw(value: PointsTo<u64>) {
            require pre.owner == Some(value);
            withdraw slot -= Some(value);
            update owner = None;
        } }
        property! { borrow(value: PointsTo<u64>) {
            require pre.owner == Some(value);
            guard slot >= Some(value);
        } }
        transition! { ping() { update marker = pre.marker + 1; } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(deposit)] fn deposit_inductive(pre:Self,post:Self,value:PointsTo<u64>) {}
        #[inductive(withdraw)] fn withdraw_inductive(pre:Self,post:Self,value:PointsTo<u64>) {}
        #[inductive(ping)] fn ping_inductive(pre:Self,post:Self) {}
    }
}

pub fn stored_cell_demo() -> (out: u64)
    ensures
        out == 9,
{
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let tracked empty = IMap::tracked_empty();
    let tracked all = StoredCell::Protocol::initialize(empty);
    let tracked (mut owner, marker) = all.split(
        StoredCell::Fragment {
            owner: Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(None)),
            marker: None,
        },
        StoredCell::Fragment {
            owner: None,
            marker: Some(vstd::resource::exclusive::ExclusiveRA::Exclusive(0nat)),
        },
    );
    let ghost original = permission;
    let tracked mut input = IMap::tracked_empty();
    proof {
        input.tracked_insert(0int, permission);
    }
    proof {
        owner = StoredCell::Protocol::deposit(owner, input, original);
    }
    let tracked guarded = StoredCell::Protocol::borrow(&owner, original);
    // This unrelated update runs while guarded storage remains borrowed.
    let tracked marker = StoredCell::Protocol::ping(marker);
    let read_before = *cell.borrow(Tracked(guarded.tracked_borrow(0int)));
    assert(read_before == 7);
    let tracked (returned_owner, mut resources) = StoredCell::Protocol::withdraw(owner, original);
    let tracked mut permission = resources.tracked_remove(0int);
    let before = cell.replace(Tracked(&mut permission), 9u64);
    assert(before == 7);
    let ghost updated = permission;
    let tracked mut input = IMap::tracked_empty();
    proof {
        input.tracked_insert(0int, permission);
    }
    let tracked owner = StoredCell::Protocol::deposit(returned_owner, input, updated);
    let tracked guarded = StoredCell::Protocol::borrow(&owner, updated);
    let after = *cell.borrow(Tracked(guarded.tracked_borrow(0int)));
    after
}

fn main() {
    let value = stored_cell_demo();
    assert(value == 9);
}

} // verus!
