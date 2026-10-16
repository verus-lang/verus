//! Two removals from one map field on one path, and storage-map guards whose
//! guarded value comes from a `have`-bound map entry, over two storage maps.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::iset::ISet;

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Tagged {
        fields {
            #[sharding(iset)]
            pub unused: ISet<int>,

            #[sharding(map)]
            pub owner: Map<int, int>,

            #[sharding(storage_map)]
            pub left: Map<int, int>,

            #[sharding(storage_map)]
            pub right: Map<int, int>,
        }

        #[invariant]
        pub fn unused_fresh(&self) -> bool {
            forall|k: int| #[trigger] self.unused.contains(k) ==>
                !self.owner.dom().contains(k) && !self.left.dom().contains(k) && !self.right.dom().contains(k)
        }

        #[invariant]
        pub fn owners_match(&self) -> bool {
            forall|k: int| #[trigger] self.owner.dom().contains(k) ==>
                self.left.dom().contains(k) && self.left[k] == self.owner[k]
                && self.right.dom().contains(k) && self.right[k] == self.owner[k]
        }

        init!{
            initialize() {
                init unused = ISet::full();
                init owner = Map::empty();
                init left = Map::empty();
                init right = Map::empty();
            }
        }

        transition!{
            insert(k: int, v: int) {
                remove unused -= set { k };
                add owner += [k => v];
                deposit left += [k => v];
                deposit right += [k => v];
            }
        }

        transition!{
            owners_distinct(k1: int, k2: int) {
                require k1 == k2;
                remove owner -= [k1 => let _];
                remove owner -= [k2 => let _];
                assert false;
            }
        }

        property!{
            guard_left(k: int) {
                have owner >= [k => let v];
                guard left >= [k => v];
            }
        }

        property!{
            guard_right(k: int) {
                have owner >= [k => let v];
                guard right >= [k => v] by {
                    assert(pre.right.dom().contains(k));
                };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, k: int, v: int) { }

        #[inductive(owners_distinct)]
        fn owners_distinct_inductive(pre: Self, post: Self, k1: int, k2: int) { }
    }
}

fn main() {}
