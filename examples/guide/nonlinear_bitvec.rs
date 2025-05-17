#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// ANCHOR: bound_checking
proof fn bound_check(x: u32, y: u32, z: u32)
    requires
        x <= 8,
        y <= 8,
{
    assert(x * y <= 100) by (nonlinear_arith)
        requires
            x <= 10,
            y <= 10;

    assert(x * y <= 1000);
}
// ANCHOR_END: bound_checking

// ANCHOR: bound_checking_func
proof fn bound_check2(x: u32, y: u32, z: u32) by (nonlinear_arith)
    requires
        x <= 8,
        y <= 8,
    ensures
        x * y <= 64
{ }
// ANCHOR_END: bound_checking_func

// ANCHOR: de_morgan
proof fn de_morgan_auto()
    by (bit_vector)
    ensures
        forall|a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b,
        forall|a: u32, b: u32| #[trigger] (!(a | b)) == !a & !b,
{
}
// ANCHOR_END: de_morgan

// ANCHOR: bitvector_easy
fn test_passes(b: u32) {
    assert(b & 7 == b % 8) by (bit_vector);
    assert(b & 0xff < 0x100) by (bit_vector);
}
// ANCHOR_END: bitvector_easy

/*
// ANCHOR: bitvector_fail
fn test_fails(x: u32, y: u32)
  requires x == y
{
  assert(x & 3 == y & 3) by(bit_vector);  // Fails
}
// ANCHOR_END: bitvector_fail
*/

// ANCHOR: bitvector_success
fn test_success(x: u32, y: u32)
    requires
        x == y,
{
    assert(x & 3 == y & 3) by (bit_vector)
        requires
            x == y,
    ;  // now x == y is available for the bit_vector proof
}
// ANCHOR_END: bitvector_success

fn main() {
}

} // verus!
