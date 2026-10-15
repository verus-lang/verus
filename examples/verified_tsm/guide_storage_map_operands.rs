//! Bulk physical map transfers operate on two real cell permissions.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

broadcast use {vstd::map::group_map_lemmas, vstd::imap::group_imap_lemmas};

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(deposit_many)]
    MapStorage {
        fields {
            #[sharding(variable)] pub auth: Map<nat, PointsTo<u64>>,
            #[sharding(storage_map)] pub stored: Map<nat, PointsTo<u64>>,
        }
        #[invariant] pub fn same(&self) -> bool { self.stored == self.auth }
        init! { initialize(value: Map<nat, PointsTo<u64>>) {
            init auth = value;
            init stored = value;
        } }
        transition! { deposit_many(value: Map<nat, PointsTo<u64>>) {
            require(pre.auth.dom().disjoint(value.dom()));
            deposit stored += (value);
            update auth = pre.auth.union_prefer_right(value);
        } }
        transition! { withdraw_many(value: Map<nat, PointsTo<u64>>) {
            require(value.submap_of(pre.auth));
            withdraw stored -= (value);
            update auth = pre.auth.remove_keys(value.dom());
        } }
        property! { guard_many(value: Map<nat, PointsTo<u64>>) {
            require(value.submap_of(pre.auth));
            guard stored >= (value);
        } }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, value: Map<nat, PointsTo<u64>>) {}
        #[inductive(deposit_many)]
        fn deposit_inductive(pre: Self, post: Self, value: Map<nat, PointsTo<u64>>) {}
        #[inductive(withdraw_many)]
        fn withdraw_inductive(pre: Self, post: Self, value: Map<nat, PointsTo<u64>>) {}
    }
}

fn physical_map_transfer() -> (out: (u64, u64))
    ensures
        out == (9u64, 11u64),
{
    let (left, Tracked(left_permission)) = PCell::new(7u64);
    let (right, Tracked(right_permission)) = PCell::new(8u64);
    let values = Ghost(Map::empty().insert(0nat, left_permission).insert(1nat, right_permission));
    let empty = Ghost(Map::<nat, PointsTo<u64>>::empty());
    let tracked mut initial = IMap::tracked_empty();
    proof {
        initial.tracked_insert(0nat, left_permission);
        initial.tracked_insert(1nat, right_permission);
        assert(initial =~= values@.to_imap());
    }
    let tracked token = MapStorage::Protocol::initialize(initial, values@);
    let tracked guard = MapStorage::Protocol::guard_many(&token, values@);
    proof {
        assert(*guard =~= values@.to_imap());
    }
    let ghost before = token.fragment();
    let tracked (token, empty_output) = MapStorage::Protocol::withdraw_many(token, empty@);
    proof {
        let (pre, post, frame) = MapStorage::Protocol::withdraw_many_witness(
            before,
            MapStorage::Fragment::unit(),
            token.fragment(),
            IMap::empty(),
            empty_output,
            empty@,
        );
        assert(IMap::empty() =~= empty@.to_imap());
    }
    proof {
        assert(empty_output.dom().is_empty());
    }
    let tracked token = MapStorage::Protocol::deposit_many_local(
        token,
        IMap::tracked_empty(),
        empty@,
    );
    let tracked empty_guard = MapStorage::Protocol::guard_many(&token, empty@);
    proof {
        assert(empty_guard.dom().is_empty());
    }
    let ghost before = token.fragment();
    let tracked (token, mut withdrawn) = MapStorage::Protocol::withdraw_many(token, values@);
    proof {
        let (pre, post, frame) = MapStorage::Protocol::withdraw_many_witness(
            before,
            MapStorage::Fragment::unit(),
            token.fragment(),
            IMap::empty(),
            withdrawn,
            values@,
        );
        assert(token.fragment().auth->Some_0->Exclusive_0 =~= Map::empty());
    }
    let tracked mut left_permission = withdrawn.tracked_remove(0nat);
    let tracked mut right_permission = withdrawn.tracked_remove(1nat);
    left.replace(Tracked(&mut left_permission), 9u64);
    right.replace(Tracked(&mut right_permission), 11u64);
    let values = Ghost(Map::empty().insert(0nat, left_permission).insert(1nat, right_permission));
    let tracked mut deposit = IMap::tracked_empty();
    proof {
        deposit.tracked_insert(0nat, left_permission);
        deposit.tracked_insert(1nat, right_permission);
        assert(deposit =~= values@.to_imap());
    }
    let tracked token = MapStorage::Protocol::deposit_many_local(token, deposit, values@);
    let tracked (_, mut withdrawn) = MapStorage::Protocol::withdraw_many(token, values@);
    let tracked left_permission = withdrawn.tracked_remove(0nat);
    let tracked right_permission = withdrawn.tracked_remove(1nat);
    (left.into_inner(Tracked(left_permission)), right.into_inner(Tracked(right_permission)))
}

fn main() {
    let result = physical_map_transfer();
    assert(result == (9u64, 11u64));
}

} // verus!
