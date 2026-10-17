//! Complete original bool relations; a ghost authority makes the resource companion sound.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;

verified_state_machine_model! { Y {
    fields {
        #[sharding(bool)]
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
            add b += true by {
                assert(pre.b == false); // FAILS
            };
        }
    }

    transition!{
        tr_have() {
            have b >= true;
        }
    }

    transition!{
        tr_remove() {
            remove b -= true;
        }
    }

    transition!{
        tr_add_gen(x: bool) {
            add b += (x) by {
                assert(pre.b == false || x == false); // FAILS
            };
        }
    }

    transition!{
        tr_have_gen(x: bool) {
            have b >= (x);
        }
    }

    transition!{
        tr_remove_gen(x: bool) {
            remove b -= (x);
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    pre.b == false ==> post.b == true
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b == false && post.b == true
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == true
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == true
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == false
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b == true && post.b == false
}

spec fn rel_tr4(pre: Y::State, post: Y::State, x: bool) -> bool {
    (!pre.b || !x) ==> (post.b == (pre.b || x))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
    (!pre.b || !x) && (post.b == (pre.b || x))
}

spec fn rel_tr5(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == pre.b)
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == pre.b)
}

spec fn rel_tr6(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == (pre.b && !x))
}

spec fn rel_tr6_strong(pre: Y::State, post: Y::State, x: bool) -> bool {
    (x ==> pre.b) && (post.b == (pre.b && !x))
}

proof fn correct_tr(pre: Y::State, post: Y::State, x: bool) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr_add(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr_have(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
            rel_tr3(pre, post) == Y::State::tr_remove(pre, post),
            rel_tr3_strong(pre, post) == Y::State::tr_remove_strong(pre, post),
            rel_tr4(pre, post, x) == Y::State::tr_add_gen(pre, post, x),
            rel_tr4_strong(pre, post, x) == Y::State::tr_add_gen_strong(pre, post, x),
            rel_tr5(pre, post, x) == Y::State::tr_have_gen(pre, post, x),
            rel_tr5_strong(pre, post, x) == Y::State::tr_have_gen_strong(pre, post, x),
            rel_tr6(pre, post, x) == Y::State::tr_remove_gen(pre, post, x),
            rel_tr6_strong(pre, post, x) == Y::State::tr_remove_gen_strong(pre, post, x),
        ],
    );
}

} // verus!
verified_tokenized_state_machine! {  SafeY {
    fields {
        #[sharding(bool)]
        pub b: bool,
        #[sharding(variable)] pub flag:bool,
    }

    init!{
        init_false() {
            init b = false;
            init flag=false;
        }
    }

    init!{
        init_true() {
            init b = true;
            init flag=true;
        }
    }

    transition!{
        tr_add() {
            require !pre.flag;
            add b += true;
            update flag=true;
        }
    }

    transition!{
        tr_have() {
            have b >= true;
        }
    }

    transition!{
        tr_remove() {
            remove b -= true;
            update flag=false;
        }
    }

    transition!{
        tr_add_gen(x: bool) {
            require !pre.flag || !x;
            add b += (x);
            update flag=pre.flag || x;
        }
    }

    transition!{
        tr_have_gen(x: bool) {
            have b >= (x);
        }
    }

    transition!{
        tr_remove_gen(x: bool) {
            remove b -= (x);
            update flag=if x {false}else{pre.flag};
        }
    }

    // This ghost authority witnesses full-state absence; local false is the unit.
    #[invariant] pub fn authority(&self)->bool {self.b==self.flag}
    #[inductive(init_false)] fn init_false_inductive(post:Self) {}
    #[inductive(init_true)] fn init_true_inductive(post:Self) {}
    #[inductive(tr_add)] fn tr_add_inductive(pre:Self,post:Self) {}
    #[inductive(tr_have)] fn tr_have_inductive(pre:Self,post:Self) {}
    #[inductive(tr_remove)] fn tr_remove_inductive(pre:Self,post:Self) {}
    #[inductive(tr_add_gen)] fn tr_add_gen_inductive(pre:Self,post:Self,x:bool) {}
    #[inductive(tr_have_gen)] fn tr_have_gen_inductive(pre:Self,post:Self,x:bool) {}
    #[inductive(tr_remove_gen)] fn tr_remove_gen_inductive(pre:Self,post:Self,x:bool) {}
}}

verus! {

pub proof fn test_inst1() {
    let tracked (Tracked(inst), Tracked(token_f), Tracked(mut flag)) =
        SafeY::Instance::init_false();
    assert(token_f is None);
    let tracked tok = inst.tr_add(&mut flag);
    assert(equal(tok.instance_id(), inst.id()));
    inst.tr_have(&tok);
    inst.tr_remove(tok, &mut flag);
    let tracked opt_tok = inst.tr_add_gen(true, &mut flag);
    assert(opt_tok is Some);
    assert(equal(opt_tok->Some_0.instance_id(), inst.id()));
    inst.tr_have_gen(true, &opt_tok);
    inst.tr_remove_gen(true, opt_tok, &mut flag);
    let tracked opt_tok = inst.tr_add_gen(false, &mut flag);
    assert(opt_tok is None);
    inst.tr_have_gen(false, &opt_tok);
    inst.tr_remove_gen(false, opt_tok, &mut flag);
}

pub proof fn test_inst2() {
    let tracked (Tracked(inst), Tracked(token_t), Tracked(flag)) = SafeY::Instance::init_true();
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
