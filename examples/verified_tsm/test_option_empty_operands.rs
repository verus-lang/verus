//! Complete empty optional-operand relation case and physical resource histories.
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verified_state_machine_model! { Y {
    fields {
        #[sharding(option)]
        pub opt: Option<int>,

        #[sharding(storage_option)]
        pub storage_opt: Option<int>,
    }

    property!{
        ro() {
            guard storage_opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr1() {
            have opt >= (Option::<int>::None);
        }
    }

    transition!{
        tr2() {
            add opt += (Option::<int>::None);
            deposit storage_opt += (Option::<int>::None);
        }
    }

    transition!{
        tr3() {
            remove opt -= (Option::<int>::None);
            withdraw storage_opt -= (Option::<int>::None);
        }
    }
}}
verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    equal(pre.opt, post.opt) && equal(pre.storage_opt, post.storage_opt)
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

proof fn correct_tr2(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2(pre, post));
    ensures(rel_tr2(pre, post));
}

proof fn rev_tr2(pre: Y::State, post: Y::State) {
    requires(rel_tr2(pre, post));
    ensures(Y::State::tr2(pre, post));
}

proof fn correct_tr2_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr2_strong(pre, post));
    ensures(rel_tr2_strong(pre, post));
}

proof fn rev_tr2_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr2_strong(pre, post));
    ensures(Y::State::tr2_strong(pre, post));
}

proof fn correct_tr3(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3(pre, post));
    ensures(rel_tr3(pre, post));
}

proof fn rev_tr3(pre: Y::State, post: Y::State) {
    requires(rel_tr3(pre, post));
    ensures(Y::State::tr3(pre, post));
}

proof fn correct_tr3_strong(pre: Y::State, post: Y::State) {
    requires(Y::State::tr3_strong(pre, post));
    ensures(rel_tr3_strong(pre, post));
}

proof fn rev_tr3_strong(pre: Y::State, post: Y::State) {
    requires(rel_tr3_strong(pre, post));
    ensures(Y::State::tr3_strong(pre, post));
}

} // verus!
fn main() {}
