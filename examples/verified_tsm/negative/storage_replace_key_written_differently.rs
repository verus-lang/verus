// EXPECTED-ERROR: unable to prove that this deposit does not replace a stored value: verified storage cannot deposit into a location withdrawn earlier in the same transition; split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs
//! Diagnostic: a deposit into a `storage_map` key withdrawn earlier in the same
//! transition, where the keys are written differently (`k` and `j`, equal by a
//! `require`). The macro cannot tell syntactically that they are equal, so the
//! machine is generated, and the storage proof fails at the deposit with the same
//! hint as the syntactic rejection (`storage_replace_same_location.rs`). The
//! transition `move_key`, of the same shape with keys that differ, verifies.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    Store {
        fields {
            #[sharding(variable)] pub vals: Map<int, int>,
            #[sharding(storage_map)] pub store: Map<int, int>,
        }

        #[invariant]
        pub fn stored(&self) -> bool { self.vals == self.store }

        init! { initialize() { init vals = Map::empty(); init store = Map::empty(); } }

        transition! {
            move_key(k: int, j: int, v: int) {
                require(k != j && pre.vals.dom().contains(k) && !pre.vals.dom().contains(j));
                withdraw store -= [k => pre.vals[k]];
                deposit store += [j => v];
                update vals = pre.vals.remove(k).insert(j, v);
            }
        }

        transition! {
            replace(k: int, j: int, v: int) {
                require(k == j && pre.vals.dom().contains(k));
                withdraw store -= [k => pre.vals[k]];
                deposit store += [j => v];
                update vals = pre.vals.insert(k, v);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(move_key)]
        fn move_key_inductive(pre: Self, post: Self, k: int, j: int, v: int) { }

        #[inductive(replace)]
        fn replace_inductive(pre: Self, post: Self, k: int, j: int, v: int) {
            assert(post.vals =~= post.store);
        }
    }
}

} // verus!
