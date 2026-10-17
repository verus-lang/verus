//! Field and index sub-updates of `variable` and `not_tokenized` fields:
//! `update p.x = e`, `update t.1.x = e`, `update m[k].y = e`,
//! `update r.s[0] = e`. Each is the whole-field update
//! `update p = Pt { x: e, ..pre.p }` (see `examples/state_machines/sub_updates.rs`).
//! The raw interface: `raw_forms_sub_updates.rs`.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verus! {

pub struct Pt {
    pub x: int,
    pub y: int,
}

pub struct Rec<A> {
    pub a: A,
    pub s: Seq<int>,
}

}

verified_tokenized_state_machine! {
    Sub {
        fields {
            #[sharding(variable)]
            pub p: Pt,

            #[sharding(variable)]
            pub t: (int, Pt),

            #[sharding(variable)]
            pub m: Map<int, Pt>,

            #[sharding(not_tokenized)]
            pub r: Rec<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.m.dom().contains(1) && self.r.s.len() == 2
        }

        init!{
            initialize() {
                init p = Pt { x: 0, y: 0 };
                init t = (0, Pt { x: 0, y: 0 });
                init m = Map::empty().insert(1, Pt { x: 0, y: 0 });
                init r = Rec { a: 0, s: Seq::empty().push(0).push(0) };
            }
        }

        transition!{
            set_p(v: int) {
                update p.x = v;
            }
        }

        transition!{
            set_t(v: int) {
                update t.1.x = v;
                update t.0 = pre.t.0 + 1;
            }
        }

        transition!{
            set_m(v: int) {
                update m[1].y = v;
            }
        }

        transition!{
            set_r(v: int) {
                update r.s[0] = v;
                update r.a = v;
            }
        }

        transition!{
            branch(c: bool, v: int) {
                if c {
                    update p.x = v;
                } else {
                    update p.y = v;
                }
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(set_p)]
        fn set_p_inductive(pre: Self, post: Self, v: int) { }

        #[inductive(set_t)]
        fn set_t_inductive(pre: Self, post: Self, v: int) { }

        #[inductive(set_m)]
        fn set_m_inductive(pre: Self, post: Self, v: int) {
            assert(post.m.dom() =~= pre.m.dom());
        }

        #[inductive(set_r)]
        fn set_r_inductive(pre: Self, post: Self, v: int) { }

        #[inductive(branch)]
        fn branch_inductive(pre: Self, post: Self, c: bool, v: int) { }
    }
}

verus! {

proof fn client() {
    let tracked (Tracked(inst), Tracked(p), Tracked(t), Tracked(m)) = Sub::Instance::initialize();
    let tracked mut p = p;
    let tracked mut t = t;
    let tracked mut m = m;
    inst.set_p(5, &mut p);
    assert(p.value() == Pt { x: 5, y: 0 });
    inst.branch(false, 7, &mut p);
    assert(p.value() == Pt { x: 5, y: 7 });
    inst.set_t(3, &mut t);
    assert(t.value().1 == Pt { x: 3, y: 0 } && t.value().0 == 1);
    inst.set_m(9, &mut m);
    assert(m.value()[1] == Pt { x: 0, y: 9 });
    inst.set_r(4);
}

}

fn main() {}
