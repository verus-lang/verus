// EXPECTED-ERROR: precondition not satisfied
//! Full persistent-option codegen case: exact relations and the original resource client.
#![allow(unused_imports)]
use verus_state_machines_macros::{verified_state_machine_model, verified_tokenized_state_machine};
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm_collections::*;

verified_state_machine_model! { Y {
    fields {
        #[sharding(persistent_option)]
        pub c: Option<int>,

        #[sharding(persistent_option)]
        pub d: Option<int>,
    }

    init!{
        initialize() {
            init c = Option::None;
            init d = Option::Some(7);
        }
    }

    transition!{
        tr1() {
            have d >= Some(7);
            add c (union)= Some(3);
        }
    }

    transition!{
        tr2() {
            add c (union)= ( Option::Some(3) );
        }
    }

    transition!{
        tr3() {
            have c >= (
                Option::Some(3)
            );
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        (match self.c {
            Option::Some(x) => x == 3,
            _ => true,
        })
        &&
        (match self.d {
            Option::Some(x) => x == 7,
            _ => true,
        })
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self) { }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    &&& pre.d == Option::Some(7)
    &&& ((match pre.c {
        Option::Some(x) => x == 3,
        Option::None => true,
    }) ==> {
        &&& pre.d == post.d
        &&& post.c == Option::Some(3)
    })
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    &&& pre.d == Option::Some(7)
    &&& ((match pre.c {
        Option::Some(x) => x == 3,
        Option::None => true,
    }) && {
        &&& pre.d == post.d
        &&& post.c == Option::Some(3)
    })
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    (match pre.c {
        Option::Some(x) => x == 3,
        Option::None => true,
    }) ==> {
        &&& pre.d == post.d
        &&& post.c == Option::Some(3)
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    &&& (match pre.c {
        Option::Some(x) => x == 3,
        Option::None => true,
    })
    &&& {
        &&& pre.d == post.d
        &&& post.c == Option::Some(3)
    }
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    &&& pre.c == Option::Some(3)
    &&& post.c == pre.c
    &&& post.d == pre.d
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    rel_tr3(pre, post)
}

proof fn correct_tr(pre: Y::State, post: Y::State) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr1(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr2(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
            rel_tr3(pre, post) == Y::State::tr3(pre, post),
            rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
        ],
    );
}

} // verus!
verified_tokenized_state_machine! {  SafeY {
    fields {
        #[sharding(persistent_option)]
        pub c: Option<int>,

        #[sharding(persistent_option)]
        pub d: Option<int>,
    }

    init!{
        initialize() {
            init c = Option::None;
            init d = Option::Some(7);
        }
    }

    transition!{
        tr1() {
            have d >= Some(7);
            add c (union)= Some(3);
        }
    }

    transition!{
        tr2() {
            add c (union)= ( Option::Some(3) );
        }
    }

    transition!{
        tr3() {
            have c >= (
                Option::Some(3)
            );
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        (match self.c {
            Option::Some(x) => x == 3,
            _ => true,
        })
        &&
        (match self.d {
            Option::Some(x) => x == 7,
            _ => true,
        })
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) { }

    #[inductive(tr1)]
    fn tr1_inductive(pre: Self, post: Self) { }

    #[inductive(tr2)]
    fn tr2_inductive(pre: Self, post: Self) { }

    #[inductive(tr3)]
    fn tr3_inductive(pre: Self, post: Self) { }
}}

verus! {

pub proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(_c), Tracked(d_opt)) = SafeY::Instance::initialize();
    let tracked d = match d_opt {
        Option::Some(d) => d,
        Option::None => proof_from_false(),
    };
    let tracked cloned = d.clone();
    assert(equal(cloned.instance_id(), inst.id()));
    assert(d.value() == 7);
    let tracked c = inst.tr1(&d);
    assert(c.value() == 3);
    assert(equal(c.instance_id(), inst.id()));
    let tracked c2_opt = inst.tr2();
    let tracked c2 = match c2_opt {
        Option::Some(c2) => c2,
        Option::None => proof_from_false(),
    };
    assert(c2.value() == 3);
    assert(equal(c2.instance_id(), inst.id()));
    let tracked c_opt = Option::Some(c);
    inst.tr3(&None);
}

fn main() {
    proof {
        test_inst();
    }
}

} // verus!
