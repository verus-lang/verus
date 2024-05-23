#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

/*
// ANCHOR: init
fn octuple(x1: i8) -> i8 {
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}
// ANCHOR_END: init

fn main() {
}

// ANCHOR: pre1
fn octuple(x1: i8) -> i8
    requires
        -64 <= x1,
        x1 < 64,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}
// ANCHOR_END: pre1

fn main() {
}

// ANCHOR: pre2
fn octuple(x1: i8) -> i8
    requires
        -16 <= x1,
        x1 < 16,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}
// ANCHOR_END: pre2

fn main() {
}

// ANCHOR: pre3
fn main() {
    let n = octuple(20);
}
// ANCHOR_END: pre3

// ANCHOR: pre4
fn main() {
    let n = octuple(10);
}
// ANCHOR_END: pre4
*/

// ANCHOR: post1
fn main() {
    let n = octuple(10);
    assert(n == 80);
}
// ANCHOR_END: post1

// ANCHOR: post2
fn octuple(x1: i8) -> (x8: i8)
    requires
        -16 <= x1,
        x1 < 16,
    ensures
        x8 == 8 * x1,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}
// ANCHOR_END: post2

} // verus!
