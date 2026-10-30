// EXPECTED-ERROR: the borrowed part of multiset field `items` must not contain an element twice
// A borrowed multiset part that may contain an element twice: shared
// references to two tokens of one element do not show that they are distinct
// resources, so the generic interface reports this at the `have` statement.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Bag {
        fields {
            #[sharding(multiset)]
            pub items: Multiset<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            forall|x: int| #[trigger] self.items.count(x) > 0 ==> x >= 0
        }

        init!{
            initialize() {
                init items = Multiset::empty();
            }
        }

        property!{
            observe(e: Multiset<int>) {
                have items >= (e);
                assert(forall|x: int| #[trigger] e.count(x) > 0 ==> x >= 0) by {
                    broadcast use vstd::multiset::group_multiset_axioms;
                };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            broadcast use vstd::multiset::group_multiset_axioms;
        }
    }
}

fn main() {}
