//! Complete persistent scalar codegen case: exact model and checked resource clients.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(persistent_bool)]
        pub b: bool,
    }

    init!{
        init_false() {
            init b = false;
        }
    }

    init!{
        init_true() {
            init b = true;
        }
    }

    transition!{
        tr_add() {
            add b (union)= true;
        }
    }

    transition!{
        tr_have() {
            have b >= true;
        }
    }

    transition!{
        tr_add_gen(x: bool) {
            add b (union)= (x);
        }
    }

    transition!{
        tr_have_gen(x: bool) {
            have b >= (x);
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    post.b == true
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    post.b == true
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == true
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == true
}

spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
    (post.b == (pre.b || x))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
    (post.b == (pre.b || x))
}

spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == pre.b)
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == pre.b)
}

proof fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr_add(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr_have(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
            rel_tr4(pre, post, x) == Y::State::tr_add_gen(pre, post, x),
            rel_tr4_strong(pre, post, x) == Y::State::tr_add_gen_strong(pre, post, x),
            rel_tr5(pre, post, x) == Y::State::tr_have_gen(pre, post, x),
            rel_tr5_strong(pre, post, x) == Y::State::tr_have_gen_strong(pre, post, x),
        ],
    );
}

pub proof fn test_inst1() {
    let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::init_false();
    assert(token_f is None);
    let tracked tok = inst.tr_add();
    assert(equal(tok.instance_id(), inst.id()));
    inst.tr_have(&tok);
    let tracked tok1 = tok.clone();
    assert(equal((tok.value(), tok.instance_id()), (tok1.value(), tok1.instance_id())));
    let tracked opt_tok = inst.tr_add_gen(true);
    assert(opt_tok is Some);
    assert(equal(opt_tok->Some_0.instance_id(), inst.id()));
    inst.tr_have_gen(true, &opt_tok);
    let tracked opt_tok = inst.tr_add_gen(false);
    assert(opt_tok is None);
    inst.tr_have_gen(false, &opt_tok);
}

pub proof fn test_inst2() {
    let tracked (Tracked(inst), Tracked(token_t)) = Y::Instance::init_true();
    assert(token_t is Some);
    assert(equal(token_t->Some_0.instance_id(), inst.id()));
}

fn main() {
    proof {
        test_inst1();
        test_inst2();
    }
}

} // verus!
