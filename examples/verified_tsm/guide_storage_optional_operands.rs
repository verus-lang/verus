//! Optional physical transfer operands, including empty transfers and guards.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    #[verified_local_ready(deposit_optional)]
    OptionalStorage {
        fields {
            #[sharding(constant)] pub cell: CellId,
            #[sharding(variable)] pub auth: Option<PointsTo<u64>>,
            #[sharding(storage_option)] pub stored: Option<PointsTo<u64>>,
        }
        #[invariant] pub fn same(&self) -> bool {
            self.stored == self.auth
                && (self.auth is Some ==> self.auth->Some_0.id() == self.cell)
        }
        init! { initialize(cell: CellId, value: Option<PointsTo<u64>>) {
            require(value is Some ==> value->Some_0.id() == cell);
            init cell = cell;
            init auth = value;
            init stored = value;
        } }
        transition! { deposit_optional(value: Option<PointsTo<u64>>) {
            require(pre.auth is None || value is None);
            require(value is Some ==> value->Some_0.id() == pre.cell);
            deposit stored += (value);
            update auth = if value is Some { value } else { pre.auth };
        } }
        transition! { withdraw_optional(value: Option<PointsTo<u64>>) {
            require(value is None || value == pre.auth);
            withdraw stored -= (value);
            update auth = if value is Some { None } else { pre.auth };
        } }
        property! { guard_optional(value: Option<PointsTo<u64>>) {
            require(value is None || value == pre.auth);
            guard stored >= (value);
        } }
        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cell: CellId, value: Option<PointsTo<u64>>) {}
        #[inductive(deposit_optional)]
        fn deposit_inductive(pre: Self, post: Self, value: Option<PointsTo<u64>>) {}
        #[inductive(withdraw_optional)]
        fn withdraw_inductive(pre: Self, post: Self, value: Option<PointsTo<u64>>) {}
    }
}

fn optional_physical_transfer() -> (out: u64)
    ensures
        out == 9u64,
{
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let ghost value = permission;
    // The machine's storage is one `IMap<__StorageKey, __StorageValue>`;
    // `__pack_stored` tags the `Option` of the `storage_option` field.
    let tracked initial = OptionalStorage::__pack_stored(Some(permission));
    let tracked token = OptionalStorage::Protocol::initialize(initial, cell.id(), Some(value));
    let tracked guard = OptionalStorage::Protocol::guard_optional(&token, Some(value));
    proof {
        assert(*guard =~= OptionalStorage::__tag_stored(Some(value)));
    }
    let ghost before = token.fragment();
    let tracked (token, empty) = OptionalStorage::Protocol::withdraw_optional(token, None);
    proof {
        let (pre, post, frame) = OptionalStorage::Protocol::withdraw_optional_witness(
            before,
            OptionalStorage::Fragment::unit(),
            token.fragment(),
            IMap::empty(),
            empty,
            None,
        );
    }
    proof {
        assert(empty =~= IMap::empty());
    }
    let tracked token = OptionalStorage::Protocol::deposit_optional_local(token, IMap::tracked_empty(), None);
    let tracked empty_guard = OptionalStorage::Protocol::guard_optional(&token, None);
    proof {
        assert(*empty_guard =~= IMap::empty());
    }
    let ghost before = token.fragment();
    let tracked (token, withdrawn) = OptionalStorage::Protocol::withdraw_optional(
        token,
        Some(value),
    );
    proof {
        let (pre, post, frame) = OptionalStorage::Protocol::withdraw_optional_witness(
            before,
            OptionalStorage::Fragment::unit(),
            token.fragment(),
            IMap::empty(),
            withdrawn,
            Some(value),
        );
        assert(token.fragment().auth->Some_0->Exclusive_0 is None);
    }
    let tracked mut withdrawn = withdrawn;
    let tracked mut permission = OptionalStorage::__unwrap_stored(
        withdrawn.tracked_remove(OptionalStorage::__StorageKey::stored),
    );
    let old = cell.replace(Tracked(&mut permission), 9u64);
    assert(old == 7u64);
    let ghost value = permission;
    let tracked deposit = OptionalStorage::__pack_stored(Some(permission));
    let tracked token = OptionalStorage::Protocol::deposit_optional_local(
        token,
        deposit,
        Some(value),
    );
    let tracked (_, withdrawn) = OptionalStorage::Protocol::withdraw_optional(
        token,
        Some(value),
    );
    let tracked mut withdrawn = withdrawn;
    let tracked permission = OptionalStorage::__unwrap_stored(
        withdrawn.tracked_remove(OptionalStorage::__StorageKey::stored),
    );
    cell.into_inner(Tracked(permission))
}

fn main() {
    let value = optional_physical_transfer();
    assert(value == 9u64);
}

} // verus!
