// Regression (5ee61140d): a storage payload containing the machine's own checked tokens
// was rejected as a cyclic self-reference (trait bound on StorageToken); negatives:
// negative/stored_own_tokens_negative_*.rs.
//! Storage payloads that contain the machine's own checked tokens.
//!
//! The vstd storage token and carrier types take the key, value and fragment
//! types as direct parameters (no trait bounds), so such a machine is an
//! ordinary cycle of datatypes that Verus's strict-positivity check accepts;
//! negative occurrences are rejected (see `negative/stored_own_tokens_*.rs`).
//! The second machine's invariant also reads a stored token's instance id.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verus! {
pub tracked struct RPayload { pub tracked t: Option<R::Token> }
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    R {
        fields {
            #[sharding(bool)]
            pub flag: bool,

            #[sharding(storage_option)]
            pub store: Option<RPayload>,
        }

        init!{
            initialize() {
                init flag = true;
                init store = None;
            }
        }
    }
}

verus! {
pub tracked struct GPayload { pub tracked t: Option<G::unused>, pub ghost id: InstanceId }

impl GPayload {
    pub open spec fn wf(&self) -> bool {
        self.t is Some ==> self.t->Some_0.instance_id() == self.id
    }
}
}

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    G {
        fields {
            #[sharding(set)]
            pub unused: Set<int>,

            #[sharding(storage_map)]
            pub store: Map<int, crate::GPayload>,

            #[sharding(storage_map)]
            pub aux: Map<int, int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            forall|k: int| #[trigger] self.unused.contains(k) ==> !self.store.dom().contains(k)
        }

        #[invariant]
        pub fn stored_wf(&self) -> bool {
            forall|k: int| #[trigger] self.store.dom().contains(k) ==> self.store[k].wf()
        }

        init!{
            initialize(free: Set<int>) {
                init unused = free;
                init store = Map::empty();
                init aux = Map::empty();
            }
        }

        transition!{
            put(k: int, p: crate::GPayload) {
                require p.wf();
                remove unused -= set { k };
                deposit store += [k => p];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: int, p: crate::GPayload) { }
    }
}

verus! {
proof fn client() {
    let free = Set::<int>::empty().insert(1).insert(2);
    let tracked (Tracked(inst), Tracked(unused)) =
        G::Instance::initialize(free, Map::tracked_empty(), Map::tracked_empty());
    let tracked mut unused = unused;
    let tracked u1 = unused.remove(1);
    let tracked u2 = unused.remove(2);
    // A token of `G` deposited into `G`'s own storage.
    let tracked p = GPayload { t: Some(u2), id: u2.instance_id() };
    inst.put(1, p, u1, p);
}
}

fn main() {}
