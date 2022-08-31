#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use builtin_macros::*;

// TODO: change this to a macro so that it can support u8, u16, u64, etc.
//
// Since &, |, ^, (bitwise)!, >>, << are uninterpreted functions for integers,
// we need basic properties(communtativity, associativity, etc) for these operators. 
// We need to choose one of the below
// 1) Make exactly the same formula using bit-vector reasoning, OR
// 2) Make "similar" formula using bit-vector reasoning, and let the lemmas below do the rest.

verus!{
#[verifier(bit_vector)]
proof fn bit_and32_auto()
    ensures
        forall |a: u32, b: u32| #[trigger] (a&b) == b&a ,
        forall |a: u32, b: u32, c:u32| #[trigger] ((a&b)&c) == a&(b&c),
        forall |a: u32| #[trigger] (a&a) == a,
        forall |a: u32| #[trigger] (a&0) == 0,
        forall |a: u32| #[trigger] (a& 0xffffffffu32) == a,
{}

#[verifier(bit_vector)]
proof fn bit_or32_auto()
    ensures
        forall |a: u32, b: u32| #[trigger] (a|b) == b|a,
        forall |a: u32, b: u32, c:u32| #[trigger] ((a|b)|c) == a|(b|c),
        forall |a: u32| #[trigger] (a|a) == a,
        forall |a: u32| #[trigger] (a|0) == a,
        forall |a: u32| #[trigger] (a| 0xffff_ffffu32) == 0xffff_ffffu32,
{}

#[verifier(bit_vector)]
proof fn bit_xor32_auto()
    ensures
        forall |a: u32, b: u32| #[trigger] (a^b) == b^a,
        forall |a: u32, b: u32, c:u32| #[trigger] ((a^b)^c) == a^(b^c),
        forall |a: u32| #[trigger] (a^a) == 0,
        forall |a: u32| #[trigger] (a^0) == a,
        forall |a: u32| #[trigger] (a^ 0xffff_ffffu32) == !a,
{}

#[verifier(bit_vector)]
proof fn bit_not32_auto()
    ensures
        forall |a: u32| #[trigger] !(!a) == a,
        !0u32 == 0xffff_ffffu32,
{}

#[verifier(bit_vector)]
proof fn bit_lshr32_auto()
    ensures
        forall |a: u32| #[trigger] (a>>0u32) == a,
{}

#[verifier(bit_vector)]
proof fn bit_shl32_auto()
    ensures
        forall |a: u32| #[trigger] (a<<0u32) == a,
{}

#[verifier(bit_vector)]
proof fn bit_property32_auto()
    ensures
        // absorb
        forall |a: u32, b: u32| #[trigger] (a & (a | b)) == a,
        forall |a: u32, b: u32| #[trigger] (a | (a & b)) == a,
        // distributive
        forall |a: u32, b: u32, c:u32| #[trigger] (a & (b | c)) == (a & b) | (a & c),
        forall |a: u32, b: u32, c:u32| #[trigger] (a & (b ^ c)) == (a & b) ^ (a & c),
        forall |a: u32, b: u32, c:u32| #[trigger] (a | (b & c)) == (a | b) & (a | c),
        // De Morgan
        forall |a: u32, b: u32| #[trigger] (!(a & b)) == !a | !b,
        forall |a: u32, b: u32| #[trigger] (!(a | b)) == !a & !b,
{}

proof fn test9(b1: u32, b2:u32, b3:u32) { 
    bit_and32_auto();

    assert(b1 & 0xff < 0x100) by(bit_vector);
    assert(0xff & b1 < 0x100);

    let zero = 0u32;
    assert(zero & b3 == 0u32);
}


} // verus!
#[verifier(external_body)]
fn main() {}