// EXPECTED-ERROR: precondition not satisfied
//! Genuine count field tokens retain the original mutable split/join API.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

verified_tokenized_state_machine! {

    X {
        fields {
            #[sharding(count)]
            pub c: nat,
        }

        init! {
            initialize() {
                init c = 9;
            }
        }
    }
}

pub proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(mut t1)) = X::Instance::initialize();
    assert(t1.count() == 9);

    let tracked t2 = t1.split(2);
    let tracked t3 = t1;
    assert(t2.count() == 2);
    assert(t3.count() == 7);
    assert(t2.instance_id() == inst.id());
    assert(t3.instance_id() == inst.id());

    let tracked mut q = t2;
    q.join(t3);
    assert(q.count() == 9);
    let tracked t4 = q.split(0);
    assert(q.count() == 9 && t4.count() == 0);
    q.join(t4);
    let tracked t5 = q.split(9);
    assert(q.count() == 0 && t5.count() == 9);
    q.join(t5);
    assert(q.count() == 9);
}

proof fn test_split_fail() {
    let tracked (Tracked(inst), Tracked(mut t1)) = X::Instance::initialize();
    let tracked t2 = t1.split(10);
}

fn main() {
}

} // verus!
