//! Complete original ISet relations and client history through checked native tokens.
//! Y retains the original unrestricted weak/strong relations, including unsafe Add.
//! SafeY retains the reviewed authority invariant; each actual Add uses the current
//! authority owner to prove absence. This is an explicit API/model adaptation.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::{iset::*, set::*};

verified_state_machine_model! { Y {
    fields {
        #[sharding(iset)]
        pub b: ISet<int>,
    }

    init!{
        initialize() {
            init b = ISet::<int>::empty().insert(19);
        }
    }

    transition!{
        tr_add() {
            add b += set { 5 }; // FAILS
        }
    }

    transition!{
        tr_have() {
            have b >= set { 5 };
        }
    }

    transition!{
        tr_remove() {
            remove b -= set { 5 };
        }
    }

    transition!{
        tr_add_gen() {
            add b += (ISet::<int>::empty().insert(6)); // FAILS
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (ISet::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_remove_gen() {
            remove b -= (ISet::<int>::empty().insert(6));
        }
    }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    !pre.b.contains(5) ==> post.b == pre.b.insert(5)
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    !pre.b.contains(5) && post.b == pre.b.insert(5)
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && pre.b == post.b
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && pre.b == post.b
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && post.b == pre.b.remove(5)
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(5) && post.b == pre.b.remove(5)
}

spec fn rel_tr4(pre: Y::State, post: Y::State) -> bool {
    !pre.b.contains(6) ==> post.b == pre.b.union(ISet::<int>::empty().insert(6))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
    !pre.b.contains(6) && post.b == pre.b.union(ISet::<int>::empty().insert(6))
}

spec fn rel_tr5(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && pre.b == post.b
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && pre.b == post.b
}

spec fn rel_tr6(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && post.b == pre.b.difference(ISet::<int>::empty().insert(6))
}

spec fn rel_tr6_strong(pre: Y::State, post: Y::State) -> bool {
    pre.b.contains(6) && post.b == pre.b.difference(ISet::<int>::empty().insert(6))
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
            rel_tr4(pre, post) == Y::State::tr_add_gen(pre, post),
            rel_tr4_strong(pre, post) == Y::State::tr_add_gen_strong(pre, post),
            rel_tr5(pre, post) == Y::State::tr_have_gen(pre, post),
            rel_tr5_strong(pre, post) == Y::State::tr_have_gen_strong(pre, post),
            rel_tr6(pre, post) == Y::State::tr_remove_gen(pre, post),
            rel_tr6_strong(pre, post) == Y::State::tr_remove_gen_strong(pre, post),
        ],
    );
}

} // verus!
verified_tokenized_state_machine! {

SafeY {
    fields {
        #[sharding(iset)]
        pub b: ISet<int>,
        #[sharding(variable)] pub authority:ISet<int>,
    }

    init!{
        initialize() {
            init b = ISet::<int>::empty().insert(19);
            init authority=ISet::<int>::empty().insert(19);
        }
    }

    transition!{
        tr_add() {
            require !pre.authority.contains(5);
            add b += set { 5 };
            update authority=pre.authority.insert(5);
        }
    }

    transition!{
        tr_have() {
            have b >= set { 5 };
        }
    }

    transition!{
        tr_remove() {
            remove b -= set { 5 };
            update authority=pre.authority.remove(5);
        }
    }

    transition!{
        tr_add_gen() {
            require pre.authority.disjoint(ISet::<int>::empty().insert(6));
            add b += (ISet::<int>::empty().insert(6));
            update authority=pre.authority.union(ISet::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (ISet::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_remove_gen() {
            remove b -= (ISet::<int>::empty().insert(6));
            update authority=pre.authority.difference(ISet::<int>::empty().insert(6));
        }
    }

    // Authority supplies the whole set, including absence facts.
    #[invariant] pub fn authority_matches(&self)->bool {self.b==self.authority}
    #[inductive(initialize)] fn initialize_inductive(post:Self) {}
    #[inductive(tr_add)] fn tr_add_inductive(pre:Self,post:Self) {}
    #[inductive(tr_have)] fn tr_have_inductive(pre:Self,post:Self) {}
    #[inductive(tr_remove)] fn tr_remove_inductive(pre:Self,post:Self) {}
    #[inductive(tr_add_gen)] fn tr_add_gen_inductive(pre:Self,post:Self) {}
    #[inductive(tr_have_gen)] fn tr_have_gen_inductive(pre:Self,post:Self) {}
    #[inductive(tr_remove_gen)] fn tr_remove_gen_inductive(pre:Self,post:Self) {}
}}

verus! {

proof fn test_inst1() {
    let tracked (Tracked(inst), Tracked(token_f), Tracked(mut authority)) =
        SafeY::Instance::initialize();
    assert(token_f.set() =~= iset![19]);
    assert(token_f.instance_id() == inst.id());

    let tracked token1 = inst.tr_add(&mut authority);
    assert(equal(token1.instance_id(), inst.id()));
    assert(token1.element() == 5);
    inst.tr_have(&token1);
    inst.tr_remove(token1, &mut authority);

    let tracked token_set = inst.tr_add_gen(&mut authority);
    assert(token_set.set() =~= iset![6]);
    assert(token_set.instance_id() == inst.id());
    inst.tr_have_gen(&token_set);
    inst.tr_remove_gen(token_set, &mut authority);
    assert(authority.value() =~= ISet::<int>::empty().insert(19));
    assert(token_f.set() =~= iset![19]);
}

} // verus!
verus! {

fn main() {
    proof {
        test_inst1();
    }
}

} // verus!
