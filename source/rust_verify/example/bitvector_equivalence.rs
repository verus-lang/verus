#[allow(unused_imports)]
use builtin::*;
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::seq::*;
use builtin_macros::*;

macro_rules! get_bit_macro {
    ($a:expr, $b:expr) => {
        {
            (0x1u32 & ($a >> $b)) == 1
        }
    }
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
spec fn equal_lower_n_bits(a:u32, b:u32, n:u32) -> bool 
    recommends n <= 32
{   
    a & sub(1u32 << n,1) == b & sub(1u32 << n,1)                     // a & (1<<n -1) == b & (1<<n -1) 
}

// bitvector translation for `equivalence_proof_increment`
// in bit-vector mode, all spec functions should be unwrapped to definition (or use macro)
#[verifier(bit_vector)]
proof fn equivalence_proof_increment_bv(a:u32, b:u32, n:u32) 
    requires
        n < 32,
        a & sub(1u32 << n,1) == b & sub(1u32 << n,1),                // equal_lower_n_bits(a,b,n)
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        a & sub(1u32 << add(n,1),1) == b & sub(1u32 << add(n,1),1),  // equal_lower_n_bits(a,b,n+1)
{}

// when we know `a` and `b` have same lowewr `n` bits, and a[n] == b[n],
// we ensure that `a` and `b` have same lowewr `n+1` bits
// wrapper of `equivalence_proof_increment_bv` for the inductive proof below(`equivalence_proof_lower_n`)
proof fn equivalence_proof_increment(a:u32, b:u32, n:u32) 
    requires
        n < 32,
        equal_lower_n_bits(a,b,n),
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        equal_lower_n_bits(a,b, add(n,1)),
{
    equivalence_proof_increment_bv(a,b,n);
}

// for the lower `n` bits, if each bit is the same,
// we ensure that `a` and `b` have same lower `n` bits
proof fn equivalence_proof_lower_n(a:u32, b:u32, n:u32) 
    requires       
        n <= 32, 
        forall |i: u32| #![auto] 
            (i < n ==> (get_bit!(a, i) == get_bit!(b, i))),
    ensures
        equal_lower_n_bits(a, b, n),
    decreases n,
{
    if n == 0 {
        assert_bitvector_by({
            ensures(a & sub(1u32 << 0,1) == b & sub(1u32 << 0,1));
        });
        // assert(equal_lower_n_bits(a,b,0));
    } else {
        equivalence_proof_lower_n(a,b, sub(n,1));   // lower `n-1` bits
        equivalence_proof_increment(a,b,sub(n,1));  // the `n`-th bit      
    }
}

proof fn equivalence_proof(a:u32, b:u32) 
    requires        
        forall|i: u32| #![auto]
            i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
    ensures
        a == b,
{
    equivalence_proof_lower_n(a,b,32);
    // at this point, we have `equal_lower_n_bits(a,b,32)`
    // now it is trivial to get `a==b`, however, we need additional call to conclude that a==b
    // this is because Verus does not reason about bitvectors unless it is explicitly specified.
    assert_bitvector_by({
        requires([
            a & sub(1u32 << 32,1) == b & sub(1u32 << 32,1)          
        ]);
        ensures(a==b);
    })
}



// This fails because of trigger not being instantiated
// #[verifier(bit_vector)]
// proof fn equivalence_proof_bv(a:u32, b:u32) 
//     requires        
//         forall|i: u32| #![auto]
//             i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
//     ensures
//         a == b,
// {}


} // verus!
