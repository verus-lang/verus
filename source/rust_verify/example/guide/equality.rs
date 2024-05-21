#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: eq1
fn equal1(x: u8, y: u8) {
    let eq1 = x == y;  // means x.eq(y) in Rust
    let eq2 = y == x;  // means y.eq(x) in Rust
    assert(eq1 ==> eq2);  // succeeds
}
// ANCHOR_END: eq1

/*
// ANCHOR: eq2
fn equal2<A: Eq>(x: A, y: A) {
    let eq1 = x == y; // means x.eq(y) in Rust
    let eq2 = y == x; // means y.eq(x) in Rust
    assert(eq1 ==> eq2); // won't work; we can't be sure that A is an equivalence relation
}
// ANCHOR_END: eq2
*/

// ANCHOR: eq3
fn equal3(x: u8, y: u8) {
    assert({
        let eq1 = x == y;
        let eq2 = y == x;
        eq1 ==> eq2
    });
}
// ANCHOR_END: eq3

fn main() {
}

} // verus!
