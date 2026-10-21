// rust_verify/tests/example.rs expect-warnings
//! Raw backend statement forms through the generic interface: several
//! removals and additions of one set or map field, and several deposits into
//! and withdrawals from one storage map, in a single transition. The generic
//! operations call the raw ones, which check each path as one exchange.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    G {
        fields {
            #[sharding(set)] pub unused: Set<int>,
            #[sharding(map)] pub owner: Map<int, int>,
            #[sharding(storage_map)] pub left: Map<int, int>,
            #[sharding(storage_map)] pub right: Map<int, int>,
        }
        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) <==> self.left.dom().contains(k)
            &&& forall|k: int| #[trigger] self.owner.dom().contains(k) ==> self.left[k] == self.owner[k]
            &&& forall|k: int| #[trigger] self.unused.contains(k) ==> !self.owner.dom().contains(k)
        }
        init!{ initialize(free: Set<int>) {
            init unused = free; init owner = Map::empty(); init left = Map::empty(); init right = Map::empty();
        } }
        transition!{ insert_two(k: int, j: int, v: int) {
            remove unused -= set { k };
            remove unused -= set { j };
            add owner += [k => v];
            add owner += [j => v];
            deposit left += [k => v];
            deposit left += [j => v];
        } }
        transition!{ take_two(k: int, j: int) {
            remove owner -= [k => let v];
            remove owner -= [j => let w];
            withdraw left -= [k => v];
            withdraw left -= [j => w];
            add unused += set { k };
            add unused += set { j };
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, free: Set<int>) {}
        #[inductive(insert_two)] fn insert_two_inductive(pre: Self, post: Self, k: int, j: int, v: int) {
            assert forall|x: int| #[trigger] post.owner.dom().contains(x) ==> post.left[x] == post.owner[x] by {
                if x == k || x == j {} else {}
            }
        }
        #[inductive(take_two)] fn take_two_inductive(pre: Self, post: Self, k: int, j: int) {}
    }
}
verus! {

proof fn client() {
    let free = Set::<int>::empty().insert(1).insert(2);
    let tracked (Tracked(inst), Tracked(unused), Tracked(owner)) =
        G::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
    let tracked mut unused = unused;
    let tracked u1 = unused.remove(1);
    let tracked u2 = unused.remove(2);
    let tracked (Tracked(o1), Tracked(o2)) = inst.insert_two(1, 2, 7, u1, u2, 7, 7);
    assert(o1.key() == 1 && o2.key() == 2 && o1.value() == 7);
    let tracked (Tracked(u1), Tracked(u2), Tracked(l1), Tracked(l2)) = inst.take_two(1, 2, o1, o2);
    assert(l1 == 7 && l2 == 7 && u1.element() == 1 && u2.element() == 2);
}

}

fn main() {}
