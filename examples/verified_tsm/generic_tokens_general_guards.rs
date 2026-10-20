//! Storage guards of general operands, and guards with several outputs.
//!
//! The trusted interface returns `&Option<V>` (or `&Map<K, V>`) for a guard
//! of a general operand; no such object exists in the guarded storage, so
//! the generic interface returns references into it instead:
//!
//! * `guard f >= (Some(v))` on a `storage_option`: `&V` (as for `Some(v)`);
//! * `guard f >= (e)` on a `storage_option`: `Option<&V>`;
//! * `guard f >= (m)` on a `storage_map`: `Map<K, &V>`, the guarded values
//!   at the keys of `m`;
//! * `guard f >= (m)` on a `storage_imap`: `IMap<K, &V>`, likewise (built key by
//!   key, so `m` needs a finite domain, stated with a `require`).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Cells {
        fields {
            #[sharding(option)]
            pub owner1: Option<u64>,

            #[sharding(option)]
            pub owner2: Option<u64>,

            #[sharding(option)]
            pub owner3: Option<u64>,

            #[sharding(storage_option)]
            pub cell1: Option<u64>,

            #[sharding(storage_option)]
            pub cell2: Option<u64>,

            #[sharding(storage_option)]
            pub cell3: Option<u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.cell1 == self.owner1 && self.cell2 == self.owner2 && self.cell3 == self.owner3
        }

        init!{
            initialize(a: u64, b: u64) {
                init owner1 = Some(a);
                init owner2 = Some(b);
                init owner3 = None;
                init cell1 = Some(a);
                init cell2 = Some(b);
                init cell3 = None;
            }
        }

        // A general operand `(Some(v))`: a reference to `v`.
        property!{
            peek_some(v: u64) {
                have owner1 >= Some(v);
                guard cell1 >= (Some(v));
            }
        }

        // A general operand `(o)`: an optional reference.
        property!{
            peek_opt2(o: Option<u64>) {
                have owner2 >= (o);
                guard cell2 >= (o);
            }
        }

        property!{
            peek_opt3(o: Option<u64>) {
                have owner3 >= (o);
                guard cell3 >= (o);
            }
        }

        // Two outputs.
        property!{
            peek_both(a: u64, b: u64) {
                have owner1 >= Some(a);
                have owner2 >= Some(b);
                guard cell1 >= Some(a);
                guard cell2 >= Some(b);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, a: u64, b: u64) { }
    }
}

verified_tokenized_state_machine! {
    Store {
        fields {
            #[sharding(map)]
            pub owners: Map<int, u64>,

            #[sharding(storage_map)]
            pub store: Map<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners
        }

        init!{
            initialize(m: Map<int, u64>) {
                init owners = m;
                init store = m;
            }
        }

        property!{
            peek_many(m: Map<int, u64>) {
                have owners >= (m);
                guard store >= (m);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: Map<int, u64>) { }
    }
}

verified_tokenized_state_machine! {
    IStore {
        fields {
            #[sharding(imap)]
            pub owners: IMap<int, u64>,

            #[sharding(storage_imap)]
            pub store: IMap<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners
        }

        init!{
            initialize(m: IMap<int, u64>) {
                require(m.dom().finite());
                init owners = m;
                init store = m;
            }
        }

        property!{
            peek_many(m: IMap<int, u64>) {
                require(m.dom().finite());
                have owners >= (m);
                guard store >= (m);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: IMap<int, u64>) { }
    }
}

verus! {

proof fn cells_client() {
    let tracked (Tracked(inst), Tracked(o1), Tracked(o2), Tracked(o3)) =
        Cells::Instance::initialize(3, 4, Some(3), Some(4), None);
    let tracked o1 = o1.tracked_unwrap();
    let tracked g: &u64 = inst.peek_some(3, &o1);
    assert(*g == 3);
    // `o3` is empty: the guard of `None` is `None`.
    let tracked none = inst.peek_opt3(None, &o3);
    assert(none is None);
    let tracked some = inst.peek_opt2(Some(4), &o2);
    assert(some is Some && *some->Some_0 == 4);
    let tracked o2 = o2.tracked_unwrap();
    let tracked (Tracked(a), Tracked(b)) = inst.peek_both(3, 4, &o1, &o2);
    assert(*a == 3 && *b == 4);
}

proof fn store_client() {
    let m = Map::<int, u64>::empty().insert(1, 10).insert(2, 20);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1int, 10u64);
    stored.tracked_insert(2int, 20u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners)) = Store::Instance::initialize(m, stored);
    assert(owners.map() =~= m);
    let tracked g = inst.peek_many(m, &owners);
    assert(g.dom() == m.dom());
    assert(m.dom().contains(2));
    assert(*g[2] == 20);
}

proof fn istore_client() {
    let m = IMap::<int, u64>::empty().insert(1, 10);
    let tracked mut stored = IMap::tracked_empty();
    stored.tracked_insert(1int, 10u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners)) = IStore::Instance::initialize(m, stored);
    assert(owners.map() =~= m);
    let tracked g = inst.peek_many(m, &owners);
    assert(g.dom() == m.dom());
    assert(m.dom().contains(1));
    assert(*g[1] == 10);
}

}

fn main() {}
