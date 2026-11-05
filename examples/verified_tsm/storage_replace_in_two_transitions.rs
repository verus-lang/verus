//! Replacing a stored value: the workaround for the checked macro's rejection of a
//! transition that withdraws from and then deposits into the same storage location.
//!
//! A transition such as
//!
//! ```text
//! transition! { replace(new: T) {
//!     withdraw cell -= Some(pre.value);
//!     deposit cell += Some(new);
//!     update value = new;
//! } }
//! ```
//!
//! (or the same with one key of a `storage_map`) is accepted by
//! `tokenized_state_machine!`, but `verified_tokenized_state_machine!` rejects it:
//! "verified storage cannot deposit into a location withdrawn earlier in the same
//! transition". The checked macro proves each transition as one exchange of storage,
//! `t ⊎ s = t' ⊎ s'` (the protocol's storage `s` and the deposit `t` before, the new
//! storage `s'` and the withdrawn values `t'` after), with disjoint unions. A replace
//! needs two values at one location in `t ⊎ s` (the old one in `s` and the new one in
//! `t`), so no such exchange exists. Proving the transition as two exchanges,
//! withdraw-then-deposit, is not possible either: the intermediate state, where the
//! location is empty, is not a state of the machine, and the other operations'
//! proofs, which quantify over every state compatible with their tokens, would have
//! to account for it.
//!
//! The workaround makes that intermediate state a state of the machine: the replace
//! becomes two transitions, `take` (withdraw, and record that the location is in
//! flight) and `put` (deposit, and record that it is stable again), and the invariant
//! covers both states. A client that calls `take` and then `put` with the same
//! tokens gets the postcondition of the single-transition replace: the old value
//! out, the new value stored, and the field tokens in the same state as before, with
//! the new value (see `replace_cell` and `replace_key` below; the in-flight state is
//! visible only between the two calls, to the holder of the tokens). Other
//! operations need not change, except that they may now observe the in-flight state
//! of a location whose token they do not hold, which their transitions exclude by
//! requiring the stable state (here: the `idle` token of a key, the `cell_busy`
//! token).
//!
//! Two machines below: one `storage_option` field (the in-flight state is a `bool`
//! variable), and one `storage_map` field (a key in flight moves from the `idle` map
//! to the `busy` map, both `map` fields whose tokens are held by the client).
//! The machines verify with both macros.
#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
#[cfg(not(verus_verified_tsm))]
use verus_state_machines_macros::tokenized_state_machine;
#[cfg(verus_verified_tsm)]
use verus_state_machines_macros::verified_tokenized_state_machine as tokenized_state_machine;
use vstd::prelude::*;

verus! {

/// A tracked payload (any tracked resource, e.g. a `PointsTo`).
pub tracked struct Payload {
    pub ghost v: int,
}

// ----------------------------------------------------------------------------
// One `storage_option` field.
tokenized_state_machine! {
    Cell {
        fields {
            /// The stored value, while stable; the last stored value, while in flight.
            #[sharding(variable)]
            pub cell_value: Payload,

            /// Whether the value is withdrawn (between `take` and `put`).
            #[sharding(variable)]
            pub cell_busy: bool,

            #[sharding(storage_option)]
            pub cell: Option<Payload>,
        }

        #[invariant]
        pub fn stored(&self) -> bool {
            &&& !self.cell_busy ==> self.cell == Some(self.cell_value)
            &&& self.cell_busy ==> self.cell is None
        }

        init! {
            initialize(p: Payload) {
                init cell_value = p;
                init cell_busy = false;
                init cell = Some(p);
            }
        }

        /// The first half of the replace: withdraw the stored value.
        transition! {
            take() {
                require(!pre.cell_busy);
                update cell_busy = true;
                withdraw cell -= Some(pre.cell_value);
            }
        }

        /// The second half: deposit the new value.
        transition! {
            put(p: Payload) {
                require(pre.cell_busy);
                update cell_busy = false;
                update cell_value = p;
                deposit cell += Some(p);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, p: Payload) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, p: Payload) { }
    }
}

/// The replace a single `withdraw cell -= Some(..); deposit cell += Some(..)` transition
/// would provide, as `take` then `put`.
pub proof fn replace_cell(
    tracked inst: &Cell::Instance,
    tracked value: &mut Cell::cell_value,
    tracked busy: &mut Cell::cell_busy,
    tracked new: Payload,
) -> (tracked prev: Payload)
    requires
        old(value).instance_id() == inst.id(),
        old(busy).instance_id() == inst.id(),
        !old(busy).value(),
    ensures
        prev == old(value).value(),
        final(value).instance_id() == inst.id(),
        final(value).value() == new,
        final(busy).instance_id() == inst.id(),
        !final(busy).value(),
{
    let tracked prev = inst.take(value, busy);
    inst.put(new, value, busy, new);
    prev
}

pub proof fn cell_client() {
    let tracked (Tracked(inst), Tracked(mut value), Tracked(mut busy)) =
        Cell::Instance::initialize(Payload { v: 1 }, Some(Payload { v: 1 }));
    let tracked old = replace_cell(&inst, &mut value, &mut busy, Payload { v: 2 });
    assert(old.v == 1);
    let tracked old = replace_cell(&inst, &mut value, &mut busy, Payload { v: 3 });
    assert(old.v == 2);
    assert(value.value().v == 3);
}

// ----------------------------------------------------------------------------
// One key of a `storage_map` field.
tokenized_state_machine! {
    Store {
        fields {
            /// The stable keys, with their stored values.
            #[sharding(map)]
            pub idle: Map<int, Payload>,

            /// The keys in flight (between `take` and `put`), with their last values.
            #[sharding(map)]
            pub busy: Map<int, Payload>,

            #[sharding(storage_map)]
            pub store: Map<int, Payload>,
        }

        #[invariant]
        pub fn stored(&self) -> bool {
            &&& forall|k: int| #[trigger] self.idle.dom().contains(k) ==>
                    self.store.dom().contains(k) && self.store[k] == self.idle[k]
                    && !self.busy.dom().contains(k)
            &&& forall|k: int| #[trigger] self.busy.dom().contains(k) ==>
                    !self.store.dom().contains(k)
            &&& forall|k: int| #[trigger] self.store.dom().contains(k) ==>
                    self.idle.dom().contains(k)
        }

        init! {
            initialize(p1: Payload, p2: Payload) {
                init idle = Map::empty().insert(1, p1).insert(2, p2);
                init busy = Map::empty();
                init store = Map::empty().insert(1, p1).insert(2, p2);
            }
        }

        /// The first half of the replace of key `k`.
        transition! {
            take(k: int) {
                remove idle -= [k => let p];
                add busy += [k => p];
                withdraw store -= [k => p];
            }
        }

        /// The second half.
        transition! {
            put(k: int, p: Payload) {
                remove busy -= [k => let _];
                add idle += [k => p];
                deposit store += [k => p];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, p1: Payload, p2: Payload) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self, k: int) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: int, p: Payload) { }
    }
}

/// The replace of the value at `idle.key()`, as `take` then `put`.
pub proof fn replace_key(
    tracked inst: &Store::Instance,
    tracked idle: Store::idle,
    tracked new: Payload,
) -> (tracked out: (Store::idle, Payload))
    requires
        idle.instance_id() == inst.id(),
    ensures
        out.0.instance_id() == inst.id(),
        out.0.key() == idle.key(),
        out.0.value() == new,
        out.1 == idle.value(),
{
    let k = idle.key();
    let tracked (Tracked(busy), Tracked(old)) = inst.take(k, idle);
    let tracked idle = inst.put(k, new, busy, new);
    (idle, old)
}

pub proof fn store_client() {
    let tracked p1 = Payload { v: 10 };
    let tracked p2 = Payload { v: 20 };
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1, p1);
    stored.tracked_insert(2, p2);
    assert(stored =~= Map::empty().insert(1, p1).insert(2, p2));
    let tracked (Tracked(inst), Tracked(mut idle), Tracked(_busy)) =
        Store::Instance::initialize(p1, p2, stored);
    let tracked a = idle.remove(1);
    let tracked b = idle.remove(2);
    let tracked (a, old) = replace_key(&inst, a, Payload { v: 11 });
    assert(old.v == 10);
    let tracked (b, old) = replace_key(&inst, b, Payload { v: 21 });
    assert(old.v == 20);
    assert(a.key() == 1 && a.value().v == 11);
    assert(b.key() == 2 && b.value().v == 21);
}

} // verus!

fn main() {}
