#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::{imap::*, map::*, modes::*, pervasive::*, set::*};
verified_tokenized_state_machine! {  Y {
    fields {
        #[sharding(variable)]
        pub x: int,

        #[sharding(variable)]
        pub y: int,
    }

    init!{
        initialize(x: int, y: int) {
            init x = x;
            init y = y;
        }
    }

    transition!{
        upd() {
            if pre.x == 0 {
                update y = 1;
            } else {
                update y = 2;
            }
        }
    }

    transition!{
        req() {
            if pre.x == 0 {
                require(pre.y == 1);
                update y = 20;
            } else {
                require(pre.y == 2);
                update y = 25;
            }
        }
    }
}}

verus! {

proof fn test1() {
    let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(0, 0);
    inst.upd(&x, &mut y);
    assert(y.value() == 1);
}

proof fn test2() {
    let tracked (Tracked(inst), Tracked(x), Tracked(mut y)) = Y::Instance::initialize(12, 0);
    inst.upd(&x, &mut y);
    assert(y.value() == 2);
}

} // verus!
fn main() {}
