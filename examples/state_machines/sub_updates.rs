// rust_verify/tests/example.rs
//! Field and index sub-updates: `update p.x = e`, `update t.0 = e`,
//! `update m[k].x = e`, `update p.s[k] = e`, and their compositions.
//!
//! A field step `.f` is a struct update `S { f: .., ..pre.p }` (also for
//! tuple structs, `.0`), and rebuilds the tuple for a tuple type. The macro
//! only knows types syntactically: the field's declared type, tuple
//! elements, and the values of `Map`/`IMap`/`Seq`. So `update p.a.b = e`
//! with `a` a struct field is rejected; update `p.a` as a whole instead.
use verus_state_machines_macros::*;
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

pub struct Pair(pub int, pub bool);

state_machine! {
    Plain {
        fields {
            pub p: Pt,
            pub r: Rec<int>,
            pub t: (int, Pt),
            pub q: Pair,
            pub m: Map<int, Pt>,
        }

        init! {
            initialize() {
                init p = Pt { x: 0, y: 0 };
                init r = Rec { a: 0, s: Seq::empty().push(0).push(0) };
                init t = (0, Pt { x: 0, y: 0 });
                init q = Pair(0, false);
                init m = Map::empty().insert(1, Pt { x: 0, y: 0 });
            }
        }

        transition! {
            set_p(v: int) {
                update p.x = v;
            }
        }

        // Several sub-updates of one field compose in order.
        transition! {
            set_both(v: int, w: int) {
                update p.x = v;
                update p.y = w;
                update p.x = v + 1;
            }
        }

        transition! {
            set_r(v: int) {
                require(pre.r.s.len() == 2);
                update r.a = v;
                update r.s[1] = v;
            }
        }

        transition! {
            set_t(v: int) {
                update t.1.y = v;
                update t.0 = v;
            }
        }

        transition! {
            set_q(b: bool) {
                update q.1 = b;
            }
        }

        transition! {
            set_m(k: int, v: int) {
                require(pre.m.dom().contains(k));
                update m[k].y = v;
            }
        }

        transition! {
            branch(c: bool, v: int) {
                if c {
                    update p.x = v;
                } else {
                    update p.y = v;
                }
            }
        }
    }
}

proof fn plain_steps(pre: Plain::State, post: Plain::State, v: int, w: int, k: int, b: bool)
{
    if Plain::State::set_p(pre, post, v) {
        assert(post.p.x == v && post.p.y == pre.p.y);
    }
    if Plain::State::set_both(pre, post, v, w) {
        assert(post.p == Pt { x: v + 1, y: w });
    }
    if Plain::State::set_r(pre, post, v) {
        assert(post.r.a == v && post.r.s[1] == v && post.r.s[0] == pre.r.s[0]);
    }
    if Plain::State::set_t(pre, post, v) {
        assert(post.t.0 == v && post.t.1.y == v && post.t.1.x == pre.t.1.x);
    }
    if Plain::State::set_q(pre, post, b) {
        assert(post.q.1 == b && post.q.0 == pre.q.0);
    }
    if Plain::State::set_m(pre, post, k, v) {
        assert(post.m[k].y == v && post.m[k].x == pre.m[k].x);
        assert(post.m.dom() =~= pre.m.dom());
    }
    if Plain::State::branch(pre, post, false, v) {
        assert(post.p.x == pre.p.x && post.p.y == v);
    }
}

tokenized_state_machine! {
    Tok {
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

        init! {
            initialize() {
                init p = Pt { x: 0, y: 0 };
                init t = (0, Pt { x: 0, y: 0 });
                init m = Map::empty().insert(1, Pt { x: 0, y: 0 });
                init r = Rec { a: 0, s: Seq::empty().push(0).push(0) };
            }
        }

        transition! {
            set_p(v: int) {
                update p.x = v;
            }
        }

        // Sub-updates of one field in one block compose in order (they
        // become one whole-field update).
        transition! {
            set_both(v: int, w: int) {
                update p.x = v;
                update p.y = w;
                update p.x = v + 1;
            }
        }

        transition! {
            set_t(v: int) {
                update t.1.x = v;
            }
        }

        transition! {
            set_m(v: int) {
                update m[1].y = v;
                update m[1].x = pre.m[1].x + 1;
            }
        }

        transition! {
            set_r(v: int) {
                update r.s[0] = v;
            }
        }

        transition! {
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

        #[inductive(set_both)]
        fn set_both_inductive(pre: Self, post: Self, v: int, w: int) { }

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

proof fn tok_client() {
    let tracked (Tracked(inst), Tracked(mut p), Tracked(mut t), Tracked(mut m)) =
        Tok::Instance::initialize();
    inst.set_p(5, &mut p);
    assert(p.value() == Pt { x: 5, y: 0 });
    inst.branch(false, 7, &mut p);
    assert(p.value() == Pt { x: 5, y: 7 });
    inst.set_both(1, 2, &mut p);
    assert(p.value() == Pt { x: 2, y: 2 });
    inst.set_t(3, &mut t);
    assert(t.value().1.x == 3 && t.value().0 == 0);
    inst.set_m(9, &mut m);
    assert(m.value()[1] == Pt { x: 1, y: 9 });
    inst.set_r(4);
}

fn main() {}

} // verus!
