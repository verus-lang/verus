#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::prelude::*;

verus! {


fn immut()
{
// ANCHOR: immut
let x: u32 = 0;
let immut_ref_x = &x;
assert(x == 0);
assert(*immut_ref_x == 0);
// ANCHOR_END: immut
}

// ANCHOR: mut
fn mutable_example()
{
    let y: u32 = 1;
    assert(y == 1);
    modify_y(&mut y);
    assert(y == 2);
}

fn modify_y(a: &mut u32) 
    ensures *a == 2
{
    *a = 2;
}
// ANCHOR_END: mut




fn main() {
}

} // verus!
