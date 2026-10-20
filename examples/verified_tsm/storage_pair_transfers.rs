//! Two checked physical transfers preserve both actual cell permissions.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 PhysicalPair {
    fields {
        #[sharding(variable)] pub auth:IMap<nat,PointsTo<u64>>,
        #[sharding(storage_imap)] pub stored:IMap<nat,PointsTo<u64>>,
    }
    #[invariant] pub fn same(&self)->bool {self.auth==self.stored}
    init! { initialize(old:PointsTo<u64>) {
        init auth=IMap::empty().insert(0nat,old);
        init stored=IMap::empty().insert(0nat,old);
    } }
    transition! { deposit_then_withdraw(incoming:PointsTo<u64>) {
        require(!pre.auth.contains_key(1nat));
        deposit stored += [1nat=>incoming];
        withdraw stored -= [1nat=>incoming];
    } }
    transition! { swap(old:PointsTo<u64>,incoming:PointsTo<u64>) {
        require(pre.auth==IMap::empty().insert(0nat,old));
        withdraw stored -= [0nat=>old];
        deposit stored += [1nat=>incoming];
        update auth=IMap::empty().insert(1nat,incoming);
    } }
    transition! { take(incoming:PointsTo<u64>) {
        require(pre.auth==IMap::empty().insert(1nat,incoming));
        withdraw stored -= [1nat=>incoming];
        update auth=IMap::empty();
    } }
    #[inductive(initialize)] fn initialize_inductive(post:Self,old:PointsTo<u64>) {}
    #[inductive(deposit_then_withdraw)] fn deposit_then_withdraw_inductive(
        pre:Self,post:Self,incoming:PointsTo<u64>) {
        assert(post.stored =~= pre.stored);
    }
    #[inductive(swap)] fn swap_inductive(
        pre:Self,post:Self,old:PointsTo<u64>,incoming:PointsTo<u64>) {
        assert(post.stored =~= post.auth);
    }
    #[inductive(take)] fn take_inductive(pre:Self,post:Self,incoming:PointsTo<u64>) {
        assert(post.stored =~= IMap::empty());
    }
} }

proof fn pass_ready(
    owned: PhysicalPair::Fragment,
    deposited: IMap<PhysicalPair::__StorageKey, PhysicalPair::__StorageValue>,
    incoming: PointsTo<u64>,
)
    requires
        owned.auth is Some && owned.auth->Some_0 is Exclusive,
        !owned.auth->Some_0->Exclusive_0.contains_key(1nat),
        deposited == IMap::empty().insert(PhysicalPair::__StorageKey::stored(1nat), PhysicalPair::__StorageValue::stored(incoming)),
    ensures
        PhysicalPair::Protocol::deposit_then_withdraw_requires(
            owned,
            PhysicalPair::Fragment::unit(),
            deposited,
            incoming,
        ),
{
    PhysicalPair::Fragment::op_unit(owned);
    assert forall|frame: PhysicalPair::Fragment, pre: PhysicalPair::State|
        pre.invariant() && PhysicalPair::Fragment::op(owned, frame)
            == PhysicalPair::Protocol::embed(
            pre,
        ) implies PhysicalPair::State::deposit_then_withdraw_enabled(pre, incoming)
        && PhysicalPair::State::deposit_then_withdraw_owners_enabled(
        pre,
        owned,
        PhysicalPair::Fragment::unit(),
        incoming,
    ) && deposited == PhysicalPair::State::deposit_then_withdraw_deposited(pre, incoming) by {
        assert(deposited =~= PhysicalPair::State::deposit_then_withdraw_deposited(pre, incoming));
    };
}

fn physical_pair_history() -> (out: (u64, u64))
    ensures
        out == (7u64, 8u64),
{
    let (left, Tracked(old)) = PCell::new(7u64);
    let (right, Tracked(new)) = PCell::new(8u64);
    let ghost old_value = old;
    let ghost new_value = new;
    let tracked mut initial = IMap::tracked_empty();
    proof {
        initial.tracked_insert(PhysicalPair::__StorageKey::stored(0nat), PhysicalPair::__StorageValue::stored(old));
    }
    // The storage is one `IMap<__StorageKey, __StorageValue>`: the `stored`
    // entry at `k` is under `__StorageKey::stored(k)`.
    assert(initial =~= PhysicalPair::__tag_stored(IMap::empty().insert(0nat, old_value)));
    let tracked token = PhysicalPair::Protocol::initialize(initial, old_value);
    let tracked mut deposit = IMap::tracked_empty();
    proof {
        deposit.tracked_insert(PhysicalPair::__StorageKey::stored(1nat), PhysicalPair::__StorageValue::stored(new));
    }
    proof {
        assert(deposit =~= IMap::empty().insert(PhysicalPair::__StorageKey::stored(1nat), PhysicalPair::__StorageValue::stored(new_value)));
    }
    proof {
        pass_ready(token.fragment(), deposit, new_value);
    }
    let tracked (token, returned) = PhysicalPair::Protocol::deposit_then_withdraw(
        token,
        deposit,
        new_value,
    );
    let tracked mut returned = returned;
    let tracked new = PhysicalPair::__unwrap_stored(returned.tracked_remove(PhysicalPair::__StorageKey::stored(1nat)));
    let tracked mut deposit = IMap::tracked_empty();
    proof {
        deposit.tracked_insert(PhysicalPair::__StorageKey::stored(1nat), PhysicalPair::__StorageValue::stored(new));
    }
    let tracked (token, returned) = PhysicalPair::Protocol::swap(
        token,
        deposit,
        old_value,
        new_value,
    );
    let tracked mut returned = returned;
    let tracked old = PhysicalPair::__unwrap_stored(returned.tracked_remove(PhysicalPair::__StorageKey::stored(0nat)));
    let old_value = left.into_inner(Tracked(old));
    let tracked (_, returned) = PhysicalPair::Protocol::take(token, new_value);
    let tracked mut returned = returned;
    let tracked new = PhysicalPair::__unwrap_stored(returned.tracked_remove(PhysicalPair::__StorageKey::stored(1nat)));
    let new_value = right.into_inner(Tracked(new));
    (old_value, new_value)
}

fn main() {
    let result = physical_pair_history();
    assert(result == (7, 8));
}

} // verus!
