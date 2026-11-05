//! The example machine of "What gets constructed: an example" in
//! `source/docs/state_machines/src/checked-token-interfaces.md`, which includes its
//! fields and its `fill` transition: one field of each main sharding kind (constant,
//! variable, set, map, count, persistent_set, storage_option, storage_map), and a
//! client of the generic interface.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {
    Pool {
        // ANCHOR: fields
        fields {
            #[sharding(constant)]
            pub capacity: nat,

            #[sharding(variable)]
            pub spare_full: bool,

            #[sharding(set)]
            pub free: Set<nat>,

            #[sharding(map)]
            pub owner: Map<nat, int>,

            #[sharding(count)]
            pub permits: nat,

            #[sharding(persistent_set)]
            pub used: Set<nat>,

            #[sharding(storage_option)]
            pub spare: Option<int>,

            #[sharding(storage_map)]
            pub slots: Map<nat, int>,
        }
        // ANCHOR_END: fields

        // ANCHOR: inv
        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.spare_full <==> self.spare is Some
            &&& forall|k: nat| #[trigger] self.owner.dom().contains(k)
                    <==> self.slots.dom().contains(k)
            &&& forall|k: nat| #[trigger] self.owner.dom().contains(k)
                    ==> self.slots[k] == self.owner[k] && self.used.contains(k)
            &&& forall|k: nat| #[trigger] self.free.contains(k) ==> !self.owner.dom().contains(k)
            &&& forall|k: nat| #[trigger] self.used.contains(k) ==> k < self.capacity
        }
        // ANCHOR_END: inv

        init!{
            initialize(capacity: nat, free: Set<nat>) {
                require forall|k: nat| #[trigger] free.contains(k) ==> k < capacity;
                init capacity = capacity;
                init spare_full = false;
                init free = free;
                init owner = Map::empty();
                init permits = capacity;
                init used = Set::empty();
                init spare = None;
                init slots = Map::empty();
            }
        }

        // ANCHOR: fill
        transition!{
            fill(k: nat, v: int) {
                require k < pre.capacity;
                remove free -= set { k };
                remove permits -= (1);
                add owner += [k => v];
                add used (union)= set { k };
                deposit slots += [k => v];
            }
        }
        // ANCHOR_END: fill

        transition!{
            take(k: nat) {
                remove owner -= [k => let v];
                withdraw slots -= [k => v];
                add free += set { k };
                add permits += (1);
            }
        }

        transition!{
            stash(v: int) {
                require !pre.spare_full;
                update spare_full = true;
                deposit spare += Some(v);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, capacity: nat, free: Set<nat>) { }

        #[inductive(fill)]
        fn fill_inductive(pre: Self, post: Self, k: nat, v: int) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self, k: nat) { }

        #[inductive(stash)]
        fn stash_inductive(pre: Self, post: Self, v: int) { }
    }
}

verus! {

proof fn client() {
    let tracked (Tracked(inst), Tracked(_spare_full), Tracked(free), Tracked(_owner),
        Tracked(permits), Tracked(_used)) =
        Pool::Instance::initialize(2, set![0nat, 1nat], None, Map::tracked_empty());
    let tracked mut free = free;
    let tracked mut permits = permits;
    assert(free.set().contains(0));
    let tracked f0 = free.remove(0);
    let tracked p1 = permits.split(1);
    // ANCHOR: client_fill
    let tracked (Tracked(o0), Tracked(u0)) = inst.fill(0, 7, f0, p1, 7);
    // ANCHOR_END: client_fill
    assert(o0.key() == 0 && o0.value() == 7 && u0.element() == 0);
    let tracked (Tracked(f0), Tracked(_p1), Tracked(w)) = inst.take(0, o0);
    assert(w == 7 && f0.element() == 0);
}

fn main() {
}

} // verus!
