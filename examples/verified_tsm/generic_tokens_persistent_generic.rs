//! Persistent tokens of machines with type parameters own their raw tokens
//! (a leaked `&'static` token would need the parameters to be `'static`):
//! they are not `Copy`, and `clone` duplicates them. Without storage `clone`
//! takes `&self` (`Token::duplicate`); with storage it takes `&mut self` (a
//! storage-protocol resource can only be split), and so does `weaken` of a
//! `persistent_count` token, which is then an inherent method.
//! Constants whose types mention a type parameter make the instance own its
//! descriptor (it is then not `Copy` either; `clone` duplicates it).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Log<T> {
        fields {
            #[sharding(constant)]
            pub first: T,

            #[sharding(persistent_map)]
            pub entries: Map<int, T>,

            #[sharding(persistent_count)]
            pub len: nat,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.entries.dom().contains(0) && self.entries[0] == self.first
            &&& forall|i: int| #[trigger] self.entries.dom().contains(i) ==> 0 <= i < self.len
        }

        init!{
            initialize(t: T) {
                init first = t;
                init entries = Map::empty().insert(0, t);
                init len = 1;
            }
        }

        property!{
            first_entry() {
                have entries >= [0 => let t];
                assert(t == pre.first);
            }
        }

        property!{
            bounded(i: int, t: T) {
                have entries >= [i => t];
                have len >= (1);
                assert(0 <= i);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, t: T) { }
    }
}

verified_tokenized_state_machine! {
    StoredLog<T> {
        fields {
            #[sharding(persistent_map)]
            pub entries: Map<int, T>,

            #[sharding(persistent_count)]
            pub len: nat,

            #[sharding(storage_option)]
            pub cell: Option<T>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|i: int| #[trigger] self.entries.dom().contains(i) ==> 0 <= i < self.len
            &&& self.cell is Some && self.entries.dom().contains(0) && self.entries[0] == self.cell->Some_0
        }

        init!{
            initialize(t: T) {
                init entries = Map::empty().insert(0, t);
                init len = 1;
                init cell = Some(t);
            }
        }

        property!{
            peek(t: T) {
                have entries >= [0 => t];
                guard cell >= Some(t);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, t: T) { }
    }
}

verus! {

/// No `'static` bound on `T`.
proof fn log_client<T>(t: T) {
    let tracked (Tracked(inst), Tracked(entries), Tracked(len)) = Log::Instance::<T>::initialize(t);
    let tracked inst2 = inst.clone();
    assert(inst2.id() == inst.id() && inst2.first() == t);
    let tracked e0 = entries.into_map().tracked_remove(0);
    let tracked e1 = e0.clone();
    assert(e1.key() == 0 && e1.value() == t);
    inst2.first_entry(&e1);
    let tracked l0 = len.weaken(1);
    inst.bounded(0, t, &e0, &l0);
}

proof fn stored_log_client<T>(tracked x: T) {
    let ghost t = x;
    let tracked (Tracked(inst), Tracked(entries), Tracked(len)) =
        StoredLog::Instance::<T>::initialize(t, Some(x));
    let tracked mut e0 = entries.into_map().tracked_remove(0);
    let tracked e1 = e0.clone();
    assert(e1.key() == 0 && e1.value() == t && e0.value() == t);
    let tracked g = inst.peek(t, &e1);
    assert(*g == t);
    let tracked mut len = len;
    let tracked l1 = len.weaken(1);
    assert(l1.count() == 1 && len.count() == 1);
}

}

fn main() {}
