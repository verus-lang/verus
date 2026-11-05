// Regression (bdef221a1): withdrawal keys that read unowned fields, the stored map or
// `pre` as a whole (accepted by the trusted macro, which ignores storage keys) were
// rejected by the checked backend.
//! Storage withdrawal keys evaluated in the full pre-state: a key may read the
//! stored map itself, or use `pre` as a whole (as in the trusted macro, which
//! ignores storage keys). The checked exchange's withdrawal is the difference
//! of its witness states' storage, so the key is never observed locally.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    X {
        fields {
            #[sharding(storage_imap)]
            pub v: IMap<int, int>,

            #[sharding(variable)]
            pub c: int,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.c == 0 ==> self.v == IMap::<int, int>::empty().insert(0, 1).insert(1, 5)
            &&& self.c == 1 ==> self.v == IMap::<int, int>::empty().insert(0, 1)
            &&& self.c == 0 || self.c == 1
        }

        init!{
            initialize() {
                init v = IMap::empty().insert(0, 1).insert(1, 5);
                init c = 0;
            }
        }

        // The key is the value stored at 0, read through the whole state.
        transition!{
            take() {
                require(pre.c == 0);
                withdraw v -= [{ let s = pre; s.v.index(0) } => 5] by {
                    assert(pre.v.index(0) == 1);
                };
                update c = 1;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self) {
            assert(post.v =~= IMap::<int, int>::empty().insert(0, 1));
        }
    }
}

proof fn client(tracked m: IMap<int, int>)
    requires
        m == IMap::<int, int>::empty().insert(0, 1).insert(1, 5),
{
    let tracked (inst, mut c) = X::Instance::initialize(m);
    let tracked t = inst.take(&mut c);
    assert(t == 5);
    assert(c.value() == 1);
}

fn main() {
}

} // verus!
