// EXPECTED-ERROR: cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs
//! Diagnostic: a transition that withdraws from and then deposits into the same
//! storage location (a replace) is rejected at the deposit, with a pointer to the
//! workaround (`storage_replace_in_two_transitions.rs`). Here the location is the
//! single location of a `storage_option` field, whatever the deposited value.
//! The same message is reported for the same key (same text) of a `storage_map`
//! and for general operands `(Some(..))`/`(Map::empty().insert(k, ..))`
//! (rust_verify_test `relation_codegen_special_*`).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub tracked struct Payload {
    pub ghost v: int,
}

verified_tokenized_state_machine! {
    Cell {
        fields {
            #[sharding(variable)] pub cell_value: Payload,
            #[sharding(storage_option)] pub cell: Option<Payload>,
        }

        #[invariant]
        pub fn stored(&self) -> bool { self.cell == Some(self.cell_value) }

        init! { initialize(p: Payload) { init cell_value = p; init cell = Some(p); } }

        transition! {
            replace(p: Payload) {
                withdraw cell -= Some(pre.cell_value);
                deposit cell += Some(p);
                update cell_value = p;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, p: Payload) { }

        #[inductive(replace)]
        fn replace_inductive(pre: Self, post: Self, p: Payload) { }
    }
}

} // verus!
