// EXPECTED-ERROR: a guard of a general operand of storage_imap field `right` (with other storage fields or guards) needs a finite domain
// A general guard of a `storage_imap` field that is not the only storage
// field returns `IMap<K, &V>`, built key by key: its operand needs a finite
// domain, which this machine does not state.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Homogeneous {
        fields {
            #[sharding(imap)]
            pub right_owners: IMap<int, u64>,

            #[sharding(storage_map)]
            pub left: Map<int, u64>,

            #[sharding(storage_imap)]
            pub right: IMap<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.right == self.right_owners
        }

        init!{
            initialize(l: Map<int, u64>, r: IMap<int, u64>) {
                init right_owners = r;
                init left = l;
                init right = r;
            }
        }

        property!{
            peek(r: IMap<int, u64>) {
                have right_owners >= (r);
                guard right >= (r);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, l: Map<int, u64>, r: IMap<int, u64>) { }
    }
}

fn main() {}
