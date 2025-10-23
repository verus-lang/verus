#![feature(proc_macro_hygiene)]

use vstd::prelude::*;

// ANCHOR: dual_spec
#[verus_verify(dual_spec)]
#[verus_spec(
    requires
        x < 100,
        y < 100,
    returns f(x, y)
)]
fn f(x: u32, y: u32) -> u32 {
    proof!{
        assert(true);
    }
    {
        proof!{assert(true);}
        x + y
    }
}

#[verus_verify(dual_spec)]
#[verus_spec(
    requires
        x < 100,
    returns
        f2(x),
)]
pub fn f2(x: u32) -> u32 {
    f(x, 1)
}
// ANCHOR_END: dual_spec
