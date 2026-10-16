//! Checked generic field tokens for a machine with exactly one `storage_map`
//! field: deposits, withdrawals and guards use the field's own key and value
//! types (no tagged storage carrier).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    S {
        fields {
            #[sharding(set)]
            pub free: Set<int>,

            #[sharding(map)]
            pub owner: Map<int, int>,

            #[sharding(storage_map)]
            pub store: Map<int, int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.store.dom().contains(k)
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==> self.store[k] == self.owner[k]
            &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.owner.dom().contains(k)
        }

        init!{
            initialize(free: Set<int>) {
                init free = free;
                init owner = Map::empty();
                init store = Map::empty();
            }
        }

        transition!{
            put(k: int, v: int) {
                remove free -= set { k };
                add owner += [k => v];
                deposit store += [k => v];
            }
        }

        transition!{
            take(k: int) {
                remove owner -= [k => let v];
                withdraw store -= [k => v];
                add free += set { k };
            }
        }

        property!{
            peek(k: int) {
                have owner >= [k => let v];
                guard store >= [k => v];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: int, v: int) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self, k: int) { }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(free), Tracked(owner)) =
        S::Instance::initialize(Set::<int>::empty().insert(1).insert(2), Map::tracked_empty());
    let tracked mut free = free;
    let tracked f1 = free.remove(1);
    let tracked o1 = inst.put(1, 10, f1, 10);
    assert(o1.key() == 1 && o1.value() == 10);
    let tracked g = inst.peek(1, &o1);
    assert(*g == 10);
    let tracked (Tracked(f1), Tracked(v)) = inst.take(1, o1);
    assert(v == 10 && f1.element() == 1);
    assert(owner.map() == Map::<int, int>::empty());
}
}

fn main() {}
