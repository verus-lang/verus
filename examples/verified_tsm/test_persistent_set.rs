//! Complete original persistent-set test: exact relations and all clients.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
use vstd::resource::tsm_collections::*;
use vstd::{imap::*, iset::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verified_state_machine_model! { Y {
    fields {
        #[sharding(persistent_set)]
        pub b: Set<int>,
    }

    init!{
        initialize() {
            init b = Set::<int>::empty().insert(19);
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
            add b (union)= (Set::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (Set::<int>::empty().insert(6));
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
    post.b == pre.b.union(Set::<int>::empty().insert(6))
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State) -> bool {
    post.b == pre.b.union(Set::<int>::empty().insert(6))
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

} // verus!
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 SafeY {
    fields {
        #[sharding(persistent_set)]
        pub b: Set<int>,
    }

    init!{
        initialize() {
            init b = Set::<int>::empty().insert(19);
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
            add b (union)= (Set::<int>::empty().insert(6));
        }
    }

    transition!{
        tr_have_gen() {
            have b >= (Set::<int>::empty().insert(6));
        }
    }
}}
verus! {

broadcast use {vstd::set::group_set_lemmas, vstd::iset::group_iset_lemmas};

pub proof fn have_five_ready(owned: SafeY::Fragment)
    requires
        owned.b == persistent_set_frag(ISet::empty().insert(5int)),
    ensures
        SafeY::Protocol::tr_have_requires(owned, SafeY::Fragment::unit()),
{
    SafeY::Fragment::op_unit(owned);
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(owned, frame) == SafeY::Protocol::embed(
            pre,
        ) implies SafeY::State::tr_have_enabled(pre) && SafeY::State::tr_have_owners_enabled(
        pre,
        owned,
        SafeY::Fragment::unit(),
    ) by {
        persistent_set_have_many_frame(
            owned.b,
            frame.b,
            pre.b.to_iset(),
            ISet::empty().insert(5int),
        );
    }
}

pub proof fn test_inst1() {
    let tracked token_f = SafeY::Protocol::initialize();
    let original = ISet::empty().insert(19int);
    Pointwise::extensionality(token_f.fragment().b, persistent_set_frag(original));
    assert(token_f.fragment().b == persistent_set_frag(original));
    let location = token_f.loc();
    let tracked all = SafeY::Protocol::tr_add(token_f);
    let five = SafeY::Fragment { b: persistent_set_frag(ISet::empty().insert(5int)) };
    let nineteen = SafeY::Fragment { b: persistent_set_frag(original) };
    assert(SafeY::Fragment::op(five, nineteen) == all.fragment()) by {
        Pointwise::extensionality(SafeY::Fragment::op(five, nineteen).b, all.fragment().b);
    }
    let tracked (token1, original_token) = all.split(five, nineteen);
    assert(token1.loc() == location);
    assert(token1.fragment().b.at(5int) == Some(vstd::resource::agree::AgreementRA::Agree(())));
    have_five_ready(token1.fragment());
    let tracked token1 = SafeY::Protocol::tr_have(token1);
    persistent_set_idempotent(ISet::empty().insert(5int));
    let tracked token1_clone = token1.duplicate();
    assert(token1_clone.fragment() == token1.fragment());
    assert(token1_clone.loc() == token1.loc());
    have_five_ready(token1_clone.fragment());
    let tracked token1_clone = SafeY::Protocol::tr_have(token1_clone);
    let tracked general = SafeY::Protocol::tr_add_gen(original_token);
    let six = SafeY::Fragment { b: persistent_set_frag(ISet::empty().insert(6int)) };
    assert(SafeY::Fragment::op(six, nineteen) == general.fragment()) by {
        Pointwise::extensionality(SafeY::Fragment::op(six, nineteen).b, general.fragment().b);
    }
    let tracked (token_set, original_token) = general.split(six, nineteen);
    assert(token_set.fragment().b == persistent_set_frag(ISet::empty().insert(6int)));
    assert(token_set.loc() == location);
    let owned = token_set.fragment();
    SafeY::Fragment::op_unit(owned);
    assert forall|frame: SafeY::Fragment, pre: SafeY::State|
        pre.invariant() && SafeY::Fragment::op(owned, frame) == SafeY::Protocol::embed(
            pre,
        ) implies SafeY::State::tr_have_gen_enabled(pre)
        && SafeY::State::tr_have_gen_owners_enabled(pre, owned, SafeY::Fragment::unit()) by {
        persistent_set_have_many_frame(
            owned.b,
            frame.b,
            pre.b.to_iset(),
            ISet::empty().insert(6int),
        );
    }
    let tracked token_set = SafeY::Protocol::tr_have_gen(token_set);
    let tracked combined = token1.join(token1_clone).join(token_set).join(original_token);
    combined.validate();
}

pub fn demonstration() {
    proof {
        test_inst1();
    }
}

} // verus!
fn main() {
    demonstration();
}
