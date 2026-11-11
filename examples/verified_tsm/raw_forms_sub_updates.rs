// Regression (c2fa710ed): field sub-updates (`update p.x = e`) panicked in the macros.
// The generic interface is covered by the dual-run examples/state_machines/sub_updates.rs.
//! Raw interface: field and index sub-updates (`update p.x = e`,
//! `update t.1.x = e`, `update m[k].y = e`), several of them on one field,
//! and in branches.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

pub struct Pt {
    pub x: int,
    pub y: int,
}

verified_tokenized_state_machine! {
    #[verified_raw_tokens]
    Sub {
        fields {
            #[sharding(variable)] pub p: Pt,
            #[sharding(variable)] pub t: (int, Pt),
            #[sharding(variable)] pub m: Map<int, Pt>,
        }
        #[invariant] pub fn inv(&self) -> bool { self.m.dom().contains(1) }
        init! { initialize() {
            init p = Pt { x: 0, y: 0 };
            init t = (0, Pt { x: 0, y: 0 });
            init m = Map::empty().insert(1, Pt { x: 0, y: 0 });
        } }
        transition! { set_p(v: int) { update p.x = v; } }
        transition! { set_both(v: int, w: int) {
            update p.x = v;
            update p.y = w;
        } }
        transition! { set_t(v: int) { update t.1.x = v; } }
        transition! { set_m(v: int) { update m[1].y = v; } }
        transition! { branch(c: bool, v: int) {
            if c { update p.x = v; } else { update p.y = v; }
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) {}
        #[inductive(set_p)] fn set_p_inductive(pre: Self, post: Self, v: int) {}
        #[inductive(set_both)] fn set_both_inductive(pre: Self, post: Self, v: int, w: int) {}
        #[inductive(set_t)] fn set_t_inductive(pre: Self, post: Self, v: int) {}
        #[inductive(set_m)] fn set_m_inductive(pre: Self, post: Self, v: int) {
            assert(post.m.dom() =~= pre.m.dom());
        }
        #[inductive(branch)] fn branch_inductive(pre: Self, post: Self, c: bool, v: int) {}
    }
}

proof fn client() {
    let tracked token = Sub::Protocol::initialize();
    let tracked token = Sub::Protocol::set_p(token, 5);
    let tracked token = Sub::Protocol::branch(token, false, 7);
    assert(token.fragment().p->Some_0->Exclusive_0 == Pt { x: 5, y: 7 });
    let tracked token = Sub::Protocol::set_both(token, 1, 2);
    assert(token.fragment().p->Some_0->Exclusive_0 == Pt { x: 1, y: 2 });
    let tracked token = Sub::Protocol::set_t(token, 3);
    assert(token.fragment().t->Some_0->Exclusive_0 == (0int, Pt { x: 3, y: 0 }));
    let tracked token = Sub::Protocol::set_m(token, 9);
    assert(token.fragment().m->Some_0->Exclusive_0[1] == Pt { x: 0, y: 9 });
}

fn main() {}

} // verus!
