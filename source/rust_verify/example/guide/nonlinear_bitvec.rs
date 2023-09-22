#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

verus! {

// ANCHOR: bound_checking
proof fn bound_check(x: u32, y: u32, z: u32)
    requires
        x <= 0xffff,
        y <= 0xffff,
{
    assert(x * y <= 0x100000000) by(nonlinear_arith)
        requires
            x <= 0xffff,
            y <= 0xffff,
    {
        // nonlinear_arith proof block does not have any surrounding facts by default
        // assert(z <= 0xffff);    <- Trivial, but fails since this property is not included in the `requires` clause
        assert(x * y <= 0x100000000);
    }
}
// ANCHOR_END: bound_checking

// ANCHOR: de_morgan
proof fn de_morgan_auto() by(bit_vector)
ensures
    forall |a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b,
    forall |a: u32, b: u32| #[trigger] (!(a | b)) == !a & !b,
{}
// ANCHOR_END: de_morgan

// ANCHOR: bitvector_easy
fn test_passes(b: u32) {
    assert(b & 7 == b % 8) by(bit_vector);
    assert(b & 0xff < 0x100) by(bit_vector);
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
  requires x == y
{
  assert(x & 3 == y & 3) by(bit_vector)
    requires x == y; // now x == y is available for the bit_vector proof
}
// ANCHOR_END: bitvector_success

fn main() {
}

} // verus!
