// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(count)]
        pub c: nat,
    }

    init!{
        initialize() {
            init c = 9;
        }
    }

    transition!{
        tr_add() {
            add c += (2);
        }
    }

    transition!{
        tr_have() {
            have c >= (2);
        }
    }

    transition!{
        tr_remove() {
            remove c -= (2);
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    post.c == pre.c + 2
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    post.c == pre.c + 2
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c - 2
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    pre.c >= 2 && post.c == pre.c - 2
}

proof fn correct_tr(pre: Y::State, post: Y::State) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr_add(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr_have(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
            rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
            rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),
        ],
    );
}

proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(mut t1)) = Y::Instance::initialize();
    assert(t1.count() == 9);

    let tracked t2 = t1.split(2);
    let tracked t3 = t1;

    assert(t2.count() == 2);
    assert(t3.count() == 7);

    inst.tr_have(&t2);
    inst.tr_remove(t2);

    let tracked t4 = inst.tr_add();
    assert(t4.count() == 2);

    let tracked mut q = t4;
    q.join(t3);
    assert(q.count() == 9);
}

} // verus!
verus! {

proof fn test_join_fail() {
    let tracked (Tracked(inst1), Tracked(mut t1)) = Y::Instance::initialize();
    let tracked (Tracked(inst2), Tracked(t2)) = Y::Instance::initialize();
    let tracked t = t1.join(t2);  // FAILS
}

} // verus!
fn main() {}
