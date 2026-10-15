use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(persistent_iset)]
        pub b: ISet<int>,
    }

    init!{
        initialize() {
            init b = ISet::<int>::empty().insert(19);
        }
    }

    transition!{
        tr_add() {
            add b (union)= set { 5 };
        }
    }

    transition!{
        tr_have() {
            have b >= set { 5 };
        }
    }

    transition!{
        tr_add_gen() {
            add b (union)= (ISet::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (ISet::<int>::empty().insert(6));
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    post.b == pre.b.insert(5)
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    post.b == pre.b.insert(5)
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && pre.b == post.b
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && pre.b == post.b
}

spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
    post.b == pre.b.union(ISet::<int>::empty().insert(6))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
    post.b == pre.b.union(ISet::<int>::empty().insert(6))
}

spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && pre.b == post.b
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && pre.b == post.b
}

proof fn correct_tr(pre: Y::State, post: Y::State) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr_add(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr_add_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr_have(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr_have_strong(pre, post),
            rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
            rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
            rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
            rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
        ],
    );
}

proof fn test_inst1() {
    let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::initialize();
    assert(ISet::<int>::empty().insert(19).contains(19));
    assert(token_f.set() =~= iset![19]);
    assert(token_f.instance_id() == inst.id());

    let tracked token1 = inst.tr_add();
    assert(equal(token1.instance_id(), inst.id()));
    assert(token1.element() == 5);
    inst.tr_have(&token1);

    let tracked token1_clone = token1.clone();
    assert(token1_clone.instance_id() == token1.instance_id());
    assert(token1_clone.element() == token1.element());
    inst.tr_have(&token1_clone);

    let tracked token_set = inst.tr_add_gen();
    assert(ISet::<int>::empty().insert(6).contains(6));
    assert(token_set.set() =~= iset![6]);
    assert(token_set.instance_id() == inst.id());
    inst.tr_have_gen(&token_set);
}

} // verus!
verus! {

fn main() {
    proof {
        test_inst1();
    }
}

} // verus!
