#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};

verified_tokenized_state_machine! {  Y {
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

proof fn test_transition(
    tracked inst: Y::Instance,
    tracked t1: Y::opt1,
    tracked t2: Y::opt2,
    tracked t3: Y::opt3,
    tracked t4: Y::opt4,
) {
    requires(
        [
            equal(inst.id(), t1.instance_id()),
            equal(inst.id(), t2.instance_id()),
            equal(inst.id(), t3.instance_id()),
            equal(inst.id(), t4.instance_id()),
            equal(t1.value(), Option::Some(0)),
            equal(t2.value(), Option::Some(5)),
        ],
    );

    let old_t1 = t1;
    let old_t3 = t3;

    let tracked mut t1 = t1;
    let tracked mut t3 = t3;

    inst.tr1(&mut t1, &t2, &mut t3, &t4);

    assert(equal(old_t3.value(), Option::None));
    assert(equal(t4.value(), Option::Some(5)));
    assert(equal(t1.value(), Option::None));
    assert(equal(t3.value(), Option::Some(10)));
}

proof fn test_start() {
    let tracked (Tracked(inst), Tracked(t1), Tracked(t2), Tracked(t3), Tracked(t4)) =
        Y::Instance::initialize();
    test_transition(inst, t1, t2, t3, t4);
}

} // verus!
verus! {

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut t1), Tracked(t2), Tracked(mut t3), Tracked(t4)) =
            Y::Instance::initialize();
        inst.tr1(&mut t1, &t2, &mut t3, &t4);
        inst.tr1(&mut t1, &t2, &mut t3, &t4);
        assert(t1.value() == None);
        assert(t2.value() == Some(5));
        assert(t3.value() == Some(10));
        assert(t4.value() == Some(5));
    }
}

} // verus!
