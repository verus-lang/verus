#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
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
fn modify_y(a: &mut u32) 
    ensures *a == 2
{
    *a = 2;
}

fn mutable_example()
{
    let mut y: u32 = 1;
    assert(y == 1);
    modify_y(&mut y);
    assert(y == 2);
}
// ANCHOR_END: mut

// ANCHOR: requires
fn check_and_inc(a: &mut u32) 
    requires *old(a) == 0
    ensures *a == 1
{
    *a = *a + 1;
}

fn function_requires_ensures()
{
    let mut z: u32 = 0;
    check_and_inc(&mut z);
}
// ANCHOR_END: requires

// ANCHOR: asserts
fn check_and_assert(a: &mut u32)
    requires *old(a) == 0
{
    assert(*old(a) == 0);
    *a = *a + 1;
    assert(*a == 1);
    *a = *a + 1;
    assert(*a == 2);
    assert(*old(a) == 0);
}

fn asserts() 
{
    let mut x: u32 = 0;
    check_and_assert(&mut x);
}
// ANCHOR_END: asserts

// ANCHOR: complex
fn decrease(b: &mut u32)
    requires
        *old(b) == 10,
    ensures
        *b == 0,
{
    let mut i: u32 = 0;
    while (*b > 0) 
        invariant
            *b == (10 - i),
        decreases *b,
    {
        *b = *b - 1;
        i = i + 1;
        assert(*b == (10 - i));
    }
    assert(*b == 0);
    assert(*old(b) == 10);
}

fn complex_example()
{
    let mut d: u32 = 10;
    decrease(&mut d);
    assert(d == 0);
}
// ANCHOR_END: complex


fn main() {
}

} // verus!
