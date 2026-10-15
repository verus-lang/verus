// EXPECTED-ERROR: precondition not satisfied
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, multiset::*, pervasive::*, set::*};
verus! {

pub enum Goo {
    Bar,
    Qux(u64),
    Tal(u64, u64),
}

} // verus!
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(imap)]
        pub m: IMap<int, Goo>,

        #[sharding(storage_imap)]
        pub storage_m: IMap<int, Goo>,

        #[sharding(option)]
        pub opt: Option<Goo>,

        #[sharding(storage_option)]
        pub storage_opt: Option<Goo>,
    }

    init!{
        initialize(m: IMap<int, Goo>, opt: Option<Goo>) {
            init m = m;
            init storage_m = m;
            init opt = opt;
            init storage_opt = opt;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, m: IMap<int, Goo>, opt: Option<Goo>) { }

    transition!{
        tr1() {
            remove opt -= Some(let Goo::Bar);
            withdraw storage_opt -= Some(let Goo::Bar);
        }
    }

    transition!{
        tr2() {
            remove opt -= Some(let Goo::Qux(i1));
            withdraw storage_opt -= Some(let Goo::Qux(j1));
            assert(i1 == j1);
        }
    }

    transition!{
        tr3() {
            remove opt -= Some(let Goo::Tal(i1, i2));
            withdraw storage_opt -= Some(let Goo::Tal(j1, j2));
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr4(key: int) {
            remove m -= [key => let Goo::Bar];
            withdraw storage_m -= [key => let Goo::Bar];
        }
    }

    transition!{
        tr5(key: int) {
            remove m -= [key => let Goo::Qux(i1)];
            withdraw storage_m -= [key => let Goo::Qux(j1)];
            assert(i1 == j1);
        }
    }

    transition!{
        tr6(key: int) {
            remove m -= [key => let Goo::Tal(i1, i2)];
            withdraw storage_m -= [key => let Goo::Tal(j1, j2)];
            assert(i1 == j1);
            assert(i2 == j2);
        }
    }

    transition!{
        tr7(key: int) {
            have opt >= Some(let Goo::Bar);
            have m >= [key => let Goo::Bar];
        }
    }

    transition!{
        tr8(key: int) {
            have opt >= Some(let Goo::Qux(i1));
            have m >= [key => let Goo::Qux(j1)];
            require(i1 == j1);
        }
    }

    transition!{
        tr9(key: int) {
            have opt >= Some(let Goo::Tal(i1, i2));
            have m >= [key => let Goo::Tal(j1, j2)];
            require(i1 == j1);
            require(i2 == j2);
        }
    }

    #[invariant]
    pub fn the_inv(&self) -> bool {
        equal(self.m, self.storage_m)
        && equal(self.opt, self.storage_opt)
    }

        #[inductive(tr1)]
        fn tr1_inductive(pre: Self, post: Self) { }

        #[inductive(tr2)]
        fn tr2_inductive(pre: Self, post: Self) { }

        #[inductive(tr3)]
        fn tr3_inductive(pre: Self, post: Self) { }

        #[inductive(tr4)]
        fn tr4_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr5)]
        fn tr5_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr6)]
        fn tr6_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr7)]
        fn tr7_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr8)]
        fn tr8_inductive(pre: Self, post: Self, key: int) { }

        #[inductive(tr9)]
        fn tr9_inductive(pre: Self, post: Self, key: int) { }
}}

verus! {

spec fn rel_tr1(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            match pre.storage_opt {
                Option::Some(Goo::Bar) => {
                    equal(post.opt, Option::None) && equal(post.storage_opt, Option::None) && equal(
                        post.m,
                        pre.m,
                    ) && equal(post.storage_m, pre.storage_m)
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr1_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            match pre.storage_opt {
                Option::Some(Goo::Bar) => {
                    equal(post.opt, Option::None) && equal(post.storage_opt, Option::None) && equal(
                        post.m,
                        pre.m,
                    ) && equal(post.storage_m, pre.storage_m)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr2(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            match pre.storage_opt {
                Option::Some(Goo::Qux(j1)) => {
                    (i1 == j1) ==> {
                        &&& post.opt == Option::None
                        &&& post.storage_opt == Option::None
                        &&& post.m == pre.m
                        &&& post.storage_m == pre.storage_m
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr2_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            match pre.storage_opt {
                Option::Some(Goo::Qux(j1)) => {
                    &&& i1 == j1
                    &&& post.opt == Option::None
                    &&& post.storage_opt == Option::None
                    &&& post.m == pre.m
                    &&& post.storage_m == pre.storage_m
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr3(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            match pre.storage_opt {
                Option::Some(Goo::Tal(j1, j2)) => {
                    (i1 == j1 && i2 == j2) ==> {
                        &&& post.opt == Option::None
                        &&& post.storage_opt == Option::None
                        &&& post.m == pre.m
                        &&& post.storage_m == pre.storage_m
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr3_strong(pre: Y::State, post: Y::State) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            match pre.storage_opt {
                Option::Some(Goo::Tal(j1, j2)) => {
                    &&& i1 == j1 && i2 == j2
                    &&& post.opt == Option::None
                    &&& post.storage_opt == Option::None
                    &&& post.m == pre.m
                    &&& post.storage_m == pre.storage_m
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr4(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Bar => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Bar => {
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr4_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Bar => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Bar => {
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr5(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Qux(i1) => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Qux(j1) => {
                    (i1 == j1) ==> {
                        &&& post.opt == pre.opt
                        &&& post.storage_opt == pre.storage_opt
                        &&& post.m == pre.m.remove(key)
                        &&& post.storage_m == pre.storage_m.remove(key)
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr5_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Qux(i1) => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Qux(j1) => {
                    &&& i1 == j1
                    &&& post.opt == pre.opt
                    &&& post.storage_opt == pre.storage_opt
                    &&& post.m == pre.m.remove(key)
                    &&& post.storage_m == pre.storage_m.remove(key)
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr6(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Tal(i1, i2) => {
            pre.storage_m.dom().contains(key) ==> match pre.storage_m.index(key) {
                Goo::Tal(j1, j2) => {
                    (i1 == j1 && i2 == j2) ==> {
                        &&& post.opt == pre.opt
                        &&& post.storage_opt == pre.storage_opt
                        &&& post.m == pre.m.remove(key)
                        &&& post.storage_m == pre.storage_m.remove(key)
                    }
                },
                _ => true,
            }
        },
        _ => false,
    }
}

spec fn rel_tr6_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    pre.m.dom().contains(key) && match pre.m.index(key) {
        Goo::Tal(i1, i2) => {
            pre.storage_m.dom().contains(key) && match pre.storage_m.index(key) {
                Goo::Tal(j1, j2) => {
                    i1 == j1 && i2 == j2 && equal(post.opt, pre.opt) && equal(
                        post.storage_opt,
                        pre.storage_opt,
                    ) && equal(post.m, pre.m.remove(key)) && equal(
                        post.storage_m,
                        pre.storage_m.remove(key),
                    )
                },
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr7(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Bar) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Bar => equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr7_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr7(pre, post, key)
}

spec fn rel_tr8(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Qux(i1)) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Qux(j1) => i1 == j1 && equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr8_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr8(pre, post, key)
}

spec fn rel_tr9(pre: Y::State, post: Y::State, key: int) -> bool {
    match pre.opt {
        Option::Some(Goo::Tal(i1, i2)) => {
            pre.m.dom().contains(key) && match pre.m.index(key) {
                Goo::Tal(j1, j2) => i1 == j1 && i2 == j2 && equal(post, pre),
                _ => false,
            }
        },
        _ => false,
    }
}

spec fn rel_tr9_strong(pre: Y::State, post: Y::State, key: int) -> bool {
    rel_tr9(pre, post, key)
}

proof fn correct_tr(pre: Y::State, post: Y::State, key: int) {
    ensures(
        [
            rel_tr1(pre, post) == Y::State::tr1(pre, post),
            rel_tr1_strong(pre, post) == Y::State::tr1_strong(pre, post),
            rel_tr2(pre, post) == Y::State::tr2(pre, post),
            rel_tr2_strong(pre, post) == Y::State::tr2_strong(pre, post),
            rel_tr3(pre, post) == Y::State::tr3(pre, post),
            rel_tr3_strong(pre, post) == Y::State::tr3_strong(pre, post),
            rel_tr4(pre, post, key) == Y::State::tr4(pre, post, key),
            rel_tr4_strong(pre, post, key) == Y::State::tr4_strong(pre, post, key),
            rel_tr5(pre, post, key) == Y::State::tr5(pre, post, key),
            rel_tr5_strong(pre, post, key) == Y::State::tr5_strong(pre, post, key),
            rel_tr6(pre, post, key) == Y::State::tr6(pre, post, key),
            rel_tr6_strong(pre, post, key) == Y::State::tr6_strong(pre, post, key),
            rel_tr7(pre, post, key) == Y::State::tr7(pre, post, key),
            rel_tr7_strong(pre, post, key) == Y::State::tr7_strong(pre, post, key),
            rel_tr8(pre, post, key) == Y::State::tr8(pre, post, key),
            rel_tr8_strong(pre, post, key) == Y::State::tr8_strong(pre, post, key),
            rel_tr9(pre, post, key) == Y::State::tr9(pre, post, key),
            rel_tr9_strong(pre, post, key) == Y::State::tr9_strong(pre, post, key),
        ],
    );
}

proof fn test_inst1() {
    let tracked mut p_m = IMap::tracked_empty();
    p_m.tracked_insert(1, Goo::Bar);

    let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
        imap![1 => Goo::Bar],
        Option::Some(Goo::Bar),
        p_m,
        Option::Some(Goo::Bar),
    );

    assert(m_token.dom().contains(1));
    let tracked kv = m_token.remove(1);
    let tracked o = match opt_token {
        Option::None => proof_from_false(),
        Option::Some(t) => t,
    };

    inst.tr7(1, &kv, &o);

    let tracked wi = inst.tr1(o);
    assert(equal(wi, Goo::Bar));

    let tracked wi2 = inst.tr4(1, kv);
    assert(equal(wi2, Goo::Bar));
}

proof fn test_inst2() {
    let tracked mut p_m = IMap::tracked_empty();
    p_m.tracked_insert(1, Goo::Qux(8u64));

    let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
        imap![1 => Goo::Qux(8u64)],
        Option::Some(Goo::Qux(8u64)),
        p_m,
        Option::Some(Goo::Qux(8u64)),
    );

    assert(m_token.dom().contains(1));
    let tracked kv = m_token.remove(1);
    let tracked o = match opt_token {
        Option::None => proof_from_false(),
        Option::Some(t) => t,
    };

    inst.tr8(1, &kv, &o);

    let tracked wi = inst.tr2(o);
    assert(equal(wi, Goo::Qux(8u64)));

    let tracked wi2 = inst.tr5(1, kv);
    assert(equal(wi2, Goo::Qux(8u64)));
}

proof fn test_inst3() {
    let tracked mut p_m = IMap::tracked_empty();
    p_m.tracked_insert(1, Goo::Tal(8u64, 9u64));

    let tracked (Tracked(inst), Tracked(mut m_token), Tracked(opt_token)) = Y::Instance::initialize(
        imap![1 => Goo::Tal(8u64, 9u64)],
        Option::Some(Goo::Tal(8u64, 9u64)),
        p_m,
        Option::Some(Goo::Tal(8u64, 9u64)),
    );

    assert(m_token.dom().contains(1));
    let tracked kv = m_token.remove(1);
    let tracked o = match opt_token {
        Option::None => proof_from_false(),
        Option::Some(t) => t,
    };

    inst.tr9(1, &kv, &o);

    let tracked wi = inst.tr3(o);
    assert(equal(wi, Goo::Tal(8u64, 9u64)));

    let tracked wi2 = inst.tr6(1, kv);
    assert(equal(wi2, Goo::Tal(8u64, 9u64)));
}

} // verus!
verus! {

proof fn test_precondition_have3(tracked inst: Y::Instance, tracked t: Y::opt, tracked u: Y::m) {
    requires(
        equal(t.instance_id(), inst.id()) && equal(u.instance_id(), inst.id()) && u.key() == 1
            && equal(u.value(), t.value()),
    );
    let tracked k = inst.tr8(1, &u, &t);  // FAILS
}

} // verus!
fn main() {}
