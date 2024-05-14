#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

macro_rules! get_bit_macro {
    ($a:expr, $b:expr) => {{
        (0x1u32 & ($a >> $b)) == 1
    }};
}

macro_rules! get_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit_macro!($($a)*))
    }
}
fn main() {}

// example from https://stackoverflow.com/questions/73145883/showing-equivalence-of-two-bitvectors

verus! {

// for the lower `n` bits, are `a` and `b` the same?
spec fn equal_lower_n_bits(a: u32, b: u32, n: u32) -> bool
    recommends
        n <= 32,
{
    a & sub(1u32 << n, 1) == b & sub(1u32 << n, 1)  // a & (1<<n -1) == b & (1<<n -1)

}

// bitvector translation for `equivalence_proof_increment`
// in bit-vector mode, all spec functions should be unwrapped to definition (or use macro)
#[verifier::bit_vector]
proof fn equivalence_proof_increment_bv(a: u32, b: u32, n: u32)
    requires
        n < 32,
        a & sub(1u32 << n, 1) == b & sub(1u32 << n, 1),  // equal_lower_n_bits(a,b,n)
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        a & sub(1u32 << add(n, 1), 1) == b & sub(
            1u32 << add(n, 1),
            1,
        ),  // equal_lower_n_bits(a,b,n+1)
{
}

// when we know `a` and `b` have same lowewr `n` bits, and a[n] == b[n],
// we ensure that `a` and `b` have same lowewr `n+1` bits
// wrapper of `equivalence_proof_increment_bv` for the inductive proof below(`equivalence_proof_lower_n`)
proof fn equivalence_proof_increment(a: u32, b: u32, n: u32)
    requires
        n < 32,
        equal_lower_n_bits(a, b, n),
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        equal_lower_n_bits(a, b, add(n, 1)),
{
    equivalence_proof_increment_bv(a, b, n);
}

// for the lower `n` bits, if each bit is the same,
// we ensure that `a` and `b` have same lower `n` bits
proof fn equivalence_proof_lower_n(a: u32, b: u32, n: u32)
    requires
        n <= 32,
        forall|i: u32| #![auto] (i < n ==> (get_bit!(a, i) == get_bit!(b, i))),
    ensures
        equal_lower_n_bits(a, b, n),
    decreases n,
{
    if n == 0 {
        assert(a & sub(1u32 << 0, 1) == b & sub(1u32 << 0, 1)) by (bit_vector);
        // assert(equal_lower_n_bits(a,b,0));
    } else {
        equivalence_proof_lower_n(a, b, sub(n, 1));  // lower `n-1` bits
        equivalence_proof_increment(a, b, sub(n, 1));  // the `n`-th bit
    }
}

proof fn equivalence_proof(a: u32, b: u32)
    requires
        forall|i: u32| #![auto] i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
    ensures
        a == b,
{
    equivalence_proof_lower_n(a, b, 32);
    // at this point, we have `equal_lower_n_bits(a,b,32)`
    // now it is trivial to get `a==b`, however, we need additional call to conclude that a==b
    // this is because Verus does not reason about bitvectors unless it is explicitly specified.
    assert(a == b) by (bit_vector)
        requires
            a & sub(1u32 << 32, 1) == b & sub(1u32 << 32, 1),
    ;
}

// This fails because of trigger not being instantiated
// #[verifier::bit_vector]
// proof fn equivalence_proof_bv(a:u32, b:u32)
//     requires
//         forall|i: u32| #![auto]
//             i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
//     ensures
//         a == b,
// {}
#[verifier::bit_vector]
proof fn equivalence_proof_bv(a: u32, b: u32)
    requires
        get_bit!(a, 0u32) == get_bit!(b, 0u32),
        get_bit!(a, 1u32) == get_bit!(b, 1u32),
        get_bit!(a, 2u32) == get_bit!(b, 2u32),
        get_bit!(a, 3u32) == get_bit!(b, 3u32),
        get_bit!(a, 4u32) == get_bit!(b, 4u32),
        get_bit!(a, 5u32) == get_bit!(b, 5u32),
        get_bit!(a, 6u32) == get_bit!(b, 6u32),
        get_bit!(a, 7u32) == get_bit!(b, 7u32),
        get_bit!(a, 8u32) == get_bit!(b, 8u32),
        get_bit!(a, 9u32) == get_bit!(b, 9u32),
        get_bit!(a, 10u32) == get_bit!(b, 10u32),
        get_bit!(a, 11u32) == get_bit!(b, 11u32),
        get_bit!(a, 12u32) == get_bit!(b, 12u32),
        get_bit!(a, 13u32) == get_bit!(b, 13u32),
        get_bit!(a, 14u32) == get_bit!(b, 14u32),
        get_bit!(a, 15u32) == get_bit!(b, 15u32),
        get_bit!(a, 16u32) == get_bit!(b, 16u32),
        get_bit!(a, 17u32) == get_bit!(b, 17u32),
        get_bit!(a, 18u32) == get_bit!(b, 18u32),
        get_bit!(a, 19u32) == get_bit!(b, 19u32),
        get_bit!(a, 20u32) == get_bit!(b, 20u32),
        get_bit!(a, 21u32) == get_bit!(b, 21u32),
        get_bit!(a, 22u32) == get_bit!(b, 22u32),
        get_bit!(a, 23u32) == get_bit!(b, 23u32),
        get_bit!(a, 24u32) == get_bit!(b, 24u32),
        get_bit!(a, 25u32) == get_bit!(b, 25u32),
        get_bit!(a, 26u32) == get_bit!(b, 26u32),
        get_bit!(a, 27u32) == get_bit!(b, 27u32),
        get_bit!(a, 28u32) == get_bit!(b, 28u32),
        get_bit!(a, 29u32) == get_bit!(b, 29u32),
        get_bit!(a, 30u32) == get_bit!(b, 30u32),
        get_bit!(a, 31u32) == get_bit!(b, 31u32),
    ensures
        a == b,
{
}

proof fn equivalence_proof_2(a: u32, b: u32)
    requires
        forall|i: u32| #![auto] i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
    ensures
        a == b,
{
    equivalence_proof_bv(a, b);
}

// #[verifier::spec]
// fn u32_view(u: u32) -> Seq<bool> {
//     Seq::new(32, |i: int| get_bit!(u, i as u32))
// }
// proof fn equivalence_proof_3(a:u32, b:u32)
//     requires
//         u32_view(a) == u32_view(b),
//     ensures
//         a == b,
// {
//     assert(u32_view(a).index(0) == u32_view(b).index(0));
//     // assert(get_bit!(a, 0u32) == get_bit!(b, 0u32));
//     // assert(get_bit!(a, 1u32) == get_bit!(b, 1u32));
//     equivalence_proof_bv(a,b);
// }

} // verus!
