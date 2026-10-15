//! Complete extracted substantial state-machine test; reference relations retained.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::{CountRA, Machine, Token};
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verus! {

pub ghost enum Foo {
    Bar(int),
    Qax(int),
    Duck(int),
}

} // verus!
verified_state_machine_model! { Y {
    fields {
        #[sharding(variable)]
        pub opt1: Option<int>,

        #[sharding(variable)]
        pub opt2: Option<int>,

        #[sharding(variable)]
        pub opt3: Option<int>,

        #[sharding(variable)]
        pub opt4: Option<int>,
    }

    init!{
        initialize() {
            init opt1 = Option::Some(0);
            init opt2 = Option::Some(5);
            init opt3 = Option::None;
            init opt4 = Option::Some(5);
        }
    }

    transition!{
        tr1() {
            require let (Option::Some(x), Option::Some(y)) = (pre.opt1, pre.opt2);
            assert let (Option::None, Option::Some(z)) = (pre.opt3, pre.opt4);

            assert(y == z);

            update opt1 = Option::None;
            update opt3 = Option::Some(x + y + z);
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        imply(self.opt1 is Some, (
            self.opt2 is Some
                && self.opt4 is Some
                && equal(self.opt2, self.opt4)
                && self.opt3 is None
        ))
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    match (pre.opt1, pre.opt2) {
        (Option::Some(x), Option::Some(y)) => {
            match (pre.opt3, pre.opt4) {
                (Option::None, Option::Some(z)) => {
                    y == z ==> {
                        &&& post.opt1 == Option::None
                        &&& post.opt2 == pre.opt2
                        &&& post.opt3 == Option::Some(x + y + z)
                        &&& post.opt4 == pre.opt4
                    }
                },
                _ => { true },
            }
        },
        _ => { false },
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    match (pre.opt1, pre.opt2) {
        (Option::Some(x), Option::Some(y)) => {
            match (pre.opt3, pre.opt4) {
                (Option::None, Option::Some(z)) => {
                    y == z && equal(post.opt1, Option::None) && equal(post.opt2, pre.opt2) && equal(
                        post.opt3,
                        Option::Some(x + y + z),
                    ) && equal(post.opt4, pre.opt4)
                },
                _ => { false },
            }
        },
        _ => { false },
    }
}

proof fn correct_tr1(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1(pre, post));
    ensures(rel_tr1(pre, post));
}

proof fn rev_tr1(pre: Y::State, post: Y::State) {
    requires(rel_tr1(pre, post));
    ensures(Y::State::tr1(pre, post));
}

proof fn correct_tr1_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr1_strong(pre, post));
    ensures(rel_tr1_strong(pre, post));
}

proof fn rev_tr1_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr1_strong(pre, post));
    ensures(Y::State::tr1_strong(pre, post));
}

} // verus!
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
 SafeY {
    fields {
        #[sharding(variable)]
        pub opt1: Option<int>,

        #[sharding(variable)]
        pub opt2: Option<int>,

        #[sharding(variable)]
        pub opt3: Option<int>,

        #[sharding(variable)]
        pub opt4: Option<int>,
    }

    init!{
        initialize() {
            init opt1 = Option::Some(0);
            init opt2 = Option::Some(5);
            init opt3 = Option::None;
            init opt4 = Option::Some(5);
        }
    }

    transition!{
        tr1() {
            require let (Option::Some(x), Option::Some(y)) = (pre.opt1, pre.opt2);
            assert let (Option::None, Option::Some(z)) = (pre.opt3, pre.opt4);

            assert(y == z);

            update opt1 = Option::None;
            update opt3 = Option::Some(x + y + z);
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        imply(self.opt1 is Some, (
            self.opt2 is Some
                && self.opt4 is Some
                && equal(self.opt2, self.opt4)
                && self.opt3 is None
        ))
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }
}}

verus! {

pub open spec fn first(value: Option<int>) -> SafeY::Fragment {
    SafeY::Fragment { opt1: Some(ExclusiveRA::Exclusive(value)), ..SafeY::Fragment::unit() }
}

pub open spec fn second(value: Option<int>) -> SafeY::Fragment {
    SafeY::Fragment { opt2: Some(ExclusiveRA::Exclusive(value)), ..SafeY::Fragment::unit() }
}

pub open spec fn third(value: Option<int>) -> SafeY::Fragment {
    SafeY::Fragment { opt3: Some(ExclusiveRA::Exclusive(value)), ..SafeY::Fragment::unit() }
}

pub open spec fn fourth(value: Option<int>) -> SafeY::Fragment {
    SafeY::Fragment { opt4: Some(ExclusiveRA::Exclusive(value)), ..SafeY::Fragment::unit() }
}

pub proof fn test_transition(
    tracked t1: SafeY::Token,
    tracked t2: SafeY::Token,
    tracked t3: SafeY::Token,
    tracked t4: SafeY::Token,
)
    requires
        t1.loc() == t2.loc(),
        t1.loc() == t3.loc(),
        t1.loc() == t4.loc(),
        t1.fragment() == first(Some(0)),
        t2.fragment() == second(Some(5)),
        t3.fragment().opt3 is Some,
        t3.fragment().opt3->Some_0 is Exclusive,
        t4.fragment().opt4 is Some,
        t4.fragment().opt4->Some_0 is Exclusive,
        t3.fragment() == third(t3.fragment().opt3->Some_0->Exclusive_0),
        t4.fragment() == fourth(t4.fragment().opt4->Some_0->Exclusive_0),
{
    let old_t3 = t3.fragment().opt3->Some_0->Exclusive_0;
    let old_t4 = t4.fragment().opt4->Some_0->Exclusive_0;
    let tracked mut owned = t1.join(t3);
    let tracked shared = t2.join(t4);
    owned.validate_2(&shared);
    let (frame, state) = choose|frame: SafeY::Fragment, state: SafeY::State|
        state.invariant() && SafeY::Fragment::op(
            SafeY::Fragment::op(owned.fragment(), shared.fragment()),
            frame,
        ) == SafeY::Protocol::embed(state);
    assert(old_t3 == None);
    assert(old_t4 == Some(5));
    let tracked updated = SafeY::Protocol::tr1_with_shared(owned, &shared);
    assert(updated.fragment().opt1 == Some(ExclusiveRA::Exclusive(None)));
    assert(updated.fragment().opt3 == Some(ExclusiveRA::Exclusive(Some(10))));
}

pub proof fn test_start() {
    let tracked all = SafeY::Protocol::initialize();
    let tracked (t1, rest) = all.split(
        first(Some(0)),
        SafeY::Fragment::op(second(Some(5)), SafeY::Fragment::op(third(None), fourth(Some(5)))),
    );
    let tracked (t2, rest) = rest.split(
        second(Some(5)),
        SafeY::Fragment::op(third(None), fourth(Some(5))),
    );
    let tracked (t3, t4) = rest.split(third(None), fourth(Some(5)));
    test_transition(t1, t2, t3, t4);
}

pub fn demonstration() {
    proof {
        test_start();
    }
}

} // verus!
fn main() {
    demonstration();
}
