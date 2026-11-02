// EXPECTED-ERROR: in a non-positive position
//! Negative occurrence of a token in a stored payload: must be rejected.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verus! {
pub tracked struct Payload { pub ghost f: spec_fn(C::unused) -> bool }
}

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    C {
        fields {
            #[sharding(set)]
            pub unused: Set<int>,

            #[sharding(storage_map)]
            pub store: Map<int, crate::Payload>,

            #[sharding(storage_map)]
            pub aux: Map<int, int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            forall|k: int| #[trigger] self.unused.contains(k) ==> !self.store.dom().contains(k)
        }

        init!{
            initialize(free: Set<int>) {
                init unused = free;
                init store = Map::empty();
                init aux = Map::empty();
            }
        }

        transition!{
            put(k: int, p: crate::Payload) {
                remove unused -= set { k };
                deposit store += [k => p];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: int, p: crate::Payload) { }
    }
}

fn main() {}
