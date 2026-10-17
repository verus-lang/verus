// EXPECTED-ERROR: precondition not satisfied
//! Complete persistent scalar codegen case: exact model and checked resource clients.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(persistent_count)]
        pub c: nat,
    }

    init!{
        initialize() {
            init c = 9;
        }
    }

    transition!{
        tr_add() {
            add c (union)= (2);
        }
    }

    transition!{
        tr_have() {
            have c >= (2);
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    post.c == if pre.c <= 2 {
        2
    } else {
        pre.c
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    post.c == if pre.c <= 2 {
        2
    } else {
        pre.c
    }
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c
}

proof fn correct_tr(pre: Y::State, post: Y::State) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr_add(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr_have(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
        ],
    );
}

pub proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(t1)) = Y::Instance::initialize();
    let id = t1.instance_id();
    assert(t1.count() == 9);
    let tracked t2 = t1.weaken(1);
    assert(t2.count() == 1);
    inst.tr_have(&t2);
    let tracked t4 = inst.tr_add();
    assert(t4.count() == 2);
    let tracked t2_clone = t2.clone();
    assert(t2_clone.count() == t2.count());
    assert(t2_clone.instance_id() == id);
}

fn main() {
    proof {
        test_inst();
    }
}

} // verus!
