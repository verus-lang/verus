// Regression (4e0ca49ec): a guard observed through a singleton `have` failed to verify
// when preceded by another `have` of the same map field (an untriggerable quantifier
// over a pair of conditions and fragment).
//! A property that borrows a general operand and a singleton of one `map`
//! field (or two singletons), and also guards storage, on the default
//! interface. The raw interface: `raw_forms_map_mixed_have_guard.rs`.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Mixed {
        fields {
            #[sharding(map)] pub owners: Map<nat, u64>,
            #[sharding(storage_map)] pub store: Map<nat, u64>,
        }
        #[invariant] pub fn same(&self) -> bool { self.owners == self.store }
        init! { initialize(m: Map<nat, u64>) { init owners = m; init store = m; } }
        property! { peek(m: Map<nat, u64>, k: nat, v: u64) {
            have owners >= (m);
            have owners >= [k => v];
            guard store >= [k => v];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, m: Map<nat, u64>) {}
    }
}

verified_tokenized_state_machine! {
    TwoSingletons {
        fields {
            #[sharding(map)] pub owners: Map<nat, u64>,
            #[sharding(storage_map)] pub store: Map<nat, u64>,
        }
        #[invariant] pub fn same(&self) -> bool { self.owners == self.store }
        init! { initialize(m: Map<nat, u64>) { init owners = m; init store = m; } }
        property! { peek(j: nat, w: u64, k: nat, v: u64) {
            have owners >= [j => w];
            have owners >= [k => v];
            guard store >= [j => w];
            guard store >= [k => v];
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, m: Map<nat, u64>) {}
    }
}

verus! {

proof fn mixed_client() {
    let m = Map::<nat, u64>::empty().insert(1nat, 10u64).insert(2nat, 20u64);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1nat, 10u64);
    stored.tracked_insert(2nat, 20u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners)) = Mixed::Instance::initialize(m, stored);
    let tracked mut owners = owners;
    assert(owners.map() =~= m);
    let tracked two = owners.remove(2nat);
    let m1 = Map::<nat, u64>::empty().insert(1nat, 10u64);
    assert(owners.map() =~= m1);
    let tracked g = inst.peek(m1, 2nat, 20u64, &owners, &two);
    assert(*g == 20);
}

proof fn two_singletons_client() {
    let m = Map::<nat, u64>::empty().insert(1nat, 10u64).insert(2nat, 20u64);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1nat, 10u64);
    stored.tracked_insert(2nat, 20u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners)) = TwoSingletons::Instance::initialize(m, stored);
    let tracked mut owners = owners;
    assert(owners.map() =~= m);
    let tracked one = owners.remove(1nat);
    let tracked two = owners.remove(2nat);
    let tracked (Tracked(g1), Tracked(g2)) = inst.peek(1nat, 10u64, 2nat, 20u64, &one, &two);
    assert(*g1 == 10 && *g2 == 20);
    // Both singletons may borrow the same entry.
    let tracked (Tracked(h1), Tracked(h2)) = inst.peek(1nat, 10u64, 1nat, 10u64, &one, &one);
    assert(*h1 == 10 && *h2 == 10);
}

}

fn main() {}
