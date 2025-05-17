#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::{pervasive::*, *};

use state_machines_macros::case_on_init;
use state_machines_macros::case_on_next;
use state_machines_macros::state_machine;

state_machine! {
    B {
        fields {
            pub number: int,
        }

        pub struct InitLabel { }
        pub struct Label { }

        init!{
            initialize(label: InitLabel) {
                init number = 0;
            }
        }

        transition!{
            add(label: Label, n: int) {
                require(n % 2 == 0);
                update number = pre.number + n;
            }
        }

        #[invariant]
        pub fn is_even(&self) -> bool {
            self.number % 2 == 0
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, label: InitLabel) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, label: Label, n: int) { }
    }
}

state_machine! {
    A {
        fields {
            pub number: int,
        }

        pub type Label = B::Label;
        pub type InitLabel = B::InitLabel;

        init!{
            initialize(label: InitLabel) {
                init number = 0;
            }
        }

        transition!{
            add(label: Label, n: int) {
                update number = pre.number + n;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, label: InitLabel) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, label: Label, n: int) { }
    }
}

verus! {

spec fn interp(a: A::State) -> B::State {
    B::State { number: a.number * 2 }
}

proof fn next_refines_next(pre: A::State, post: A::State, label: B::Label) {
    requires(
        pre.invariant() && post.invariant() && interp(pre).invariant() && A::State::next(
            pre,
            post,
            label,
        ),
    );
    ensures(B::State::next(interp(pre), interp(post), label));
    reveal(A::State::next);
    match choose|step: A::Step| A::State::next_by(pre, post, label, step) {
        A::Step::add(n) => {
            assert_by(
                A::State::add(pre, post, label, n),
                {
                    reveal(A::State::next_by);
                },
            );
            B::show::add(interp(pre), interp(post), label, 2 * n);
        },
        A::Step::dummy_to_use_type_params(_) => {
            assume(false);  // TODO
        },
    }
}

proof fn next_refines_next_with_macro(pre: A::State, post: A::State, label: B::Label) {
    requires(
        pre.invariant() && post.invariant() && interp(pre).invariant() && A::State::next(
            pre,
            post,
            label,
        ),
    );
    ensures(B::State::next(interp(pre), interp(post), label));
    case_on_next!{pre, post, label, A => {
        add(n) => {
            assert(0u32 === 0u32); // test verus syntax
            B::show::add(interp(pre), interp(post), label, 2 * n);
        }
    }}
}

proof fn init_refines_init_with_macro(post: A::State, label: B::InitLabel) {
    requires(post.invariant() && A::State::init(post, label));
    ensures(B::State::init(interp(post), label));
    case_on_init!{post, label, A => {
        initialize() => {
            B::show::initialize(interp(post), label);
        }
    }}
}

} // verus!
fn main() {}
