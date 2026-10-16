//! Checked field tokens over the raw protocol (`#[verified_generic_tokens]`):
//! the trusted macro's API and specifications, with checked bodies. Covers
//! map/set tokens, a placeholder from `arbitrary()`, bulk initialization,
//! deposits/withdrawals over two storage maps, guards, borrowed inputs, and
//! an updated `not_tokenized` field.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    P {
        fields {
            #[sharding(set)]
            pub unused: Set<int>,

            #[sharding(map)]
            pub owner: Map<int, int>,

            #[sharding(storage_map)]
            pub left: Map<int, int>,

            #[sharding(storage_map)]
            pub right: Map<int, int>,

            #[sharding(not_tokenized)]
            pub count: int,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.left.dom().contains(k)
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.right.dom().contains(k)
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==>
                    self.left[k] == self.owner[k] && self.right[k] == self.owner[k]
            &&& forall|k: int| #[trigger] self.unused.contains(k) ==> !self.owner.dom().contains(k)
        }

        init!{
            initialize(free: Set<int>) {
                init unused = free;
                init owner = Map::empty();
                init left = Map::empty();
                init right = Map::empty();
                init count = 0;
            }
        }

        transition!{
            insert(k: int, v: int) {
                remove unused -= set { k };
                add owner += [k => v];
                deposit left += [k => v];
                deposit right += [k => v];
                update count = pre.count + 1;
            }
        }

        transition!{
            take(k: int) {
                remove owner -= [k => let v];
                withdraw left -= [k => v];
                withdraw right -= [k => v];
                add unused += set { k };
            }
        }

        transition!{
            two_have(k: int, e: int) {
                have owner >= [k => let v];
                have unused >= set { e };
                require v > 0;
                assert k != e;
            }
        }

        property!{
            two_prop(k: int, e: int) {
                have owner >= [k => let v];
                have unused >= set { e };
                require v > 0;
                assert k != e;
            }
        }

        property!{
            peek(k: int) {
                have owner >= [k => let v];
                guard left >= [k => v];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, k: int, v: int) { }

        #[inductive(two_have)]
        fn two_have_inductive(pre: Self, post: Self, k: int, e: int) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self, k: int) { }
    }
}

verus! {
proof fn client() {
    let free = Set::<int>::empty().insert(1).insert(2);
    let tracked (Tracked(inst), Tracked(unused), Tracked(owner)) =
        P::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
    let tracked mut unused = unused;
    assert(unused.set().contains(1));
    let tracked u1 = unused.remove(1);
    let tracked o1 = inst.insert(1, 10, u1, 10, 10);
    assert(o1.key() == 1 && o1.value() == 10);
    let tracked g = inst.peek(1, &o1);
    assert(*g == 10);
    let tracked (Tracked(u1b), Tracked(l), Tracked(r)) = inst.take(1, o1);
    assert(l == 10 && r == 10 && u1b.element() == 1);
    let tracked mut u1b = u1b;
    let tracked u2 = unused.remove(2);
    u1b.unique(&u2);
    assert(u1b.element() != u2.element());
}
}

fn main() {}
