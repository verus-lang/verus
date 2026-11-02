// Feature and regression (65bf3b660): storage fields of one payload type use the
// homogeneous carrier for any combination of fields, not only one exact shape.
//! Storage fields of different kinds (here a `storage_option` and a
//! `storage_map`) whose stored values have one type: the raw backend stores
//! them in a homogeneous carrier (keys tagged by field, values untagged). The generic interface supports it: singleton and general
//! deposits and withdrawals, and guards.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Slots {
        fields {
            // The state of the single cell: `Some(None)` empty, `Some(Some(v))` holding `v`.
            #[sharding(option)]
            pub cell_state: Option<Option<u64>>,

            // The state of each slot: `None` free, `Some(v)` holding `v`.
            #[sharding(map)]
            pub slots: Map<int, Option<u64>>,

            #[sharding(storage_option)]
            pub cell: Option<u64>,

            #[sharding(storage_map)]
            pub store: Map<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.slots.dom().contains(k) ==>
                    (self.slots[k] is Some <==> self.store.dom().contains(k))
                    && (self.slots[k] is Some ==> self.store[k] == self.slots[k]->Some_0)
            &&& forall|k: int| #[trigger] self.store.dom().contains(k) ==> self.slots.dom().contains(k)
            &&& self.cell_state is Some
            &&& (self.cell_state->Some_0 is Some <==> self.cell is Some)
            &&& (self.cell is Some ==> self.cell == self.cell_state->Some_0)
        }

        init!{
            initialize(free: Set<int>) {
                init cell_state = Some(None);
                init slots = Map::new(free, |k: int| None);
                init cell = None;
                init store = Map::empty();
            }
        }

        transition!{
            put_cell(v: u64) {
                remove cell_state -= Some(None);
                add cell_state += Some(Some(v));
                deposit cell += Some(v);
            }
        }

        transition!{
            take_cell() {
                remove cell_state -= Some(let x);
                require(x is Some);
                add cell_state += Some(None);
                withdraw cell -= Some(x->Some_0);
            }
        }

        property!{
            peek_cell() {
                have cell_state >= Some(let x);
                require(x is Some);
                guard cell >= Some(x->Some_0);
            }
        }

        transition!{
            put(k: int, v: u64) {
                remove slots -= [k => None];
                add slots += [k => Some(v)];
                deposit store += [k => v];
            }
        }

        transition!{
            take(k: int) {
                remove slots -= [k => let x];
                require(x is Some);
                add slots += [k => None];
                withdraw store -= [k => x->Some_0];
            }
        }

        property!{
            peek(k: int) {
                have slots >= [k => let x];
                require(x is Some);
                guard store >= [k => x->Some_0];
            }
        }

        transition!{
            put_many(m: Map<int, u64>) {
                remove slots -= (Map::new(m.dom(), |k: int| None::<u64>));
                add slots += (Map::new(m.dom(), |k: int| Some(m[k])));
                deposit store += (m);
            }
        }

        transition!{
            take_many(m: Map<int, u64>) {
                remove slots -= (Map::new(m.dom(), |k: int| Some(m[k])));
                add slots += (Map::new(m.dom(), |k: int| None::<u64>));
                withdraw store -= (m) by {
                    assert forall|k: int| #[trigger] m.dom().contains(k)
                        implies pre.store.dom().contains(k) && pre.store[k] == m[k] by {
                        let full = Map::new(m.dom(), |k: int| Some(m[k]));
                        assert(full.dom().contains(k));
                        assert(pre.slots.dom().contains(k) && pre.slots[k] == Some(m[k]));
                    }
                };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(put_cell)]
        fn put_cell_inductive(pre: Self, post: Self, v: u64) { }

        #[inductive(take_cell)]
        fn take_cell_inductive(pre: Self, post: Self) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: int, v: u64) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self, k: int) { }

        #[inductive(put_many)]
        fn put_many_inductive(pre: Self, post: Self, m: Map<int, u64>) {
            assert forall|k: int| #[trigger] post.slots.dom().contains(k) implies
                (post.slots[k] is Some <==> post.store.dom().contains(k))
                && (post.slots[k] is Some ==> post.store[k] == post.slots[k]->Some_0) by {
                if m.dom().contains(k) {
                    let free = Map::new(m.dom(), |k: int| None::<u64>);
                    assert(free.dom().contains(k));
                    assert(pre.slots.dom().contains(k) && pre.slots[k] is None);
                }
            }
        }

        #[inductive(take_many)]
        fn take_many_inductive(pre: Self, post: Self, m: Map<int, u64>) {
            assert forall|k: int| #[trigger] post.slots.dom().contains(k) implies
                (post.slots[k] is Some <==> post.store.dom().contains(k))
                && (post.slots[k] is Some ==> post.store[k] == post.slots[k]->Some_0) by {
                if m.dom().contains(k) {
                    let full = Map::new(m.dom(), |k: int| Some(m[k]));
                    assert(full.dom().contains(k));
                    assert(pre.slots.dom().contains(k) && pre.slots[k] == Some(m[k]));
                }
            }
        }
    }
}

verus! {

proof fn client() {
    let free = Set::<int>::empty().insert(1).insert(2).insert(3);
    let tracked (Tracked(inst), Tracked(cell_state), Tracked(slots)) =
        Slots::Instance::initialize(free, None, Map::tracked_empty());
    let tracked mut slots = slots;
    assert(slots.map().dom().contains(1));
    // The cell: deposit, guard, withdraw.
    let tracked c0 = cell_state.tracked_unwrap();
    let tracked c1 = inst.put_cell(7, c0, 7);
    let tracked g = inst.peek_cell(&c1);
    assert(*g == 7);
    let tracked (Tracked(c2), Tracked(v)) = inst.take_cell(c1);
    assert(v == 7 && c2.value() == None::<u64>);
    // One slot.
    let tracked s1 = slots.remove(1);
    let tracked s1 = inst.put(1, 10, s1, 10);
    let tracked g1 = inst.peek(1, &s1);
    assert(*g1 == 10);
    let tracked (Tracked(s1), Tracked(v1)) = inst.take(1, s1);
    assert(v1 == 10 && s1.value() == None::<u64>);
    // Several slots at once.
    let m = Map::<int, u64>::empty().insert(2, 20).insert(3, 30);
    let tracked mut in_free = MapToken::empty(inst.id());
    in_free.insert(slots.remove(2));
    in_free.insert(slots.remove(3));
    assert(Map::new(m.dom(), |k: int| None::<u64>) =~= in_free.map());
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(2int, 20u64);
    stored.tracked_insert(3int, 30u64);
    assert(stored =~= m);
    // Operations that consume no single token take a `Unit` of the instance.
    let tracked mut c2 = c2;
    let tracked u1 = inst.unit_from_cell_state(&mut c2);
    let tracked u2 = inst.unit_from_cell_state(&mut c2);
    let tracked full = inst.put_many(m, in_free, stored, u1);
    assert(full.map() =~= Map::new(m.dom(), |k: int| Some(m[k])));
    let tracked (Tracked(empty), Tracked(back)) = inst.take_many(m, full, u2);
    assert(back =~= m);
    assert(back[2] == 20);
}

}

fn main() {}
