//! `not_tokenized` fields and constants with the trusted macro's semantics:
//! a `not_tokenized` field that one transition updates is read by another
//! through `birds_eye` (the read is a ghost output of the operation), a
//! `not_tokenized` field that no transition updates is read the same way,
//! a transition reads a constant (it never changes), and a property reads
//! only a constant. The operations have the trusted macro's signatures.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;

verified_tokenized_state_machine! {
    N {
        fields {
            #[sharding(not_tokenized)]
            pub x: int,
            #[sharding(variable)]
            pub v: int,
            #[sharding(constant)]
            pub c: int,
            #[sharding(not_tokenized)]
            pub h: int,
        }
        #[invariant]
        pub fn inv(&self) -> bool { self.x >= 0 && self.v >= 0 && self.c >= 0 && self.h == 7 }
        init!{ initialize(c: int) { require(c >= 0); init x = 0; init v = 0; init c = c; init h = 7; } }
        transition!{ bump() { birds_eye let old_x = pre.x; update x = old_x + 1; } }
        transition!{ set_x(n: nat) { update x = n as int; } }
        transition!{ observe() { birds_eye let y = pre.x; update v = y; } }
        transition!{ add_c() { update v = pre.v + pre.c; } }
        property!{ c_nonneg() { assert(pre.c >= 0); } }
        transition!{ read_h() { birds_eye let hh = pre.h; update v = hh; } }
        property!{ h_is_7() { birds_eye let hh = pre.h; assert(hh == 7); } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, c: int) { }
        #[inductive(bump)] fn bump_inductive(pre: Self, post: Self) { }
        #[inductive(set_x)] fn set_x_inductive(pre: Self, post: Self, n: nat) { }
        #[inductive(observe)] fn observe_inductive(pre: Self, post: Self) { }
        #[inductive(add_c)] fn add_c_inductive(pre: Self, post: Self) { }
        #[inductive(read_h)] fn read_h_inductive(pre: Self, post: Self) { }
    }
}

verus! {
proof fn client() {
    let tracked (Tracked(inst), Tracked(mut v)) = N::Instance::initialize(5);
    inst.bump();
    inst.set_x(3);
    let ghost y = inst.observe(&mut v);
    assert(v.value() == y);
    inst.add_c(&mut v);
    assert(v.value() == y + 5);
    inst.c_nonneg();
    let ghost hh = inst.read_h(&mut v);
    assert(v.value() == hh);
    let ghost h2 = inst.h_is_7();
    assert(h2 == 7);
}
}
fn main() {}
