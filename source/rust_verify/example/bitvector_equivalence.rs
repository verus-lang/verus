#[allow(unused_imports)]
use builtin::*;
mod pervasive;
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
spec fn equal_lower_n_bits(a:u32, b:u32, n:u32) -> bool {
    a & sub(1u32 << n,1) == b & sub(1u32 << n,1)                     // a & (1<<n -1) == b & (1<<n -1) 
}

#[verifier(bit_vector)]
proof fn equivalence_proof_increment_bv(a:u32, b:u32, n:u32) 
    requires
        n < 32,
        a & sub(1u32 << n,1) == b & sub(1u32 << n,1),                // equal_lower_n_bits(a,b,n)
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        a & sub(1u32 << add(n,1),1) == b & sub(1u32 << add(n,1),1),  // equal_lower_n_bits(a,b,n+1)
{}

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

proof fn equivalence_proof_lower_n(a:u32, b:u32, n:u32) 
    requires       
        n < 32, 
        forall |i: u32| #![auto] 
            (i < n ==> (get_bit!(a, i) == get_bit!(b, i))),
    ensures
        equal_lower_n_bits(a, b, n),
    decreases n,
{
    if n == 0 {
        assert_bit_vector(a & sub(1u32 << 0,1) == b & sub(1u32 << 0,1));
        assert(equal_lower_n_bits(a,b,0));
    } else {
        equivalence_proof_lower_n(a,b, sub(n,1));
        equivalence_proof_increment(a,b,sub(n,1));        
    }
}

#[verifier(bit_vector)]
proof fn equivalence_proof_msb(a:u32, b:u32, n:u32) 
    requires
        n == 31,
        a & sub(1u32 << n,1) == b & sub(1u32 << n,1),                // equal_lower_n_bits(a,b,31)
        get_bit!(a, n) == get_bit!(b, n),
    ensures
        a == b,
{}

proof fn equivalence_proof(a:u32, b:u32) 
    requires        
        forall|i: u32| #![auto]
            i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
    ensures
        a == b,
{
    equivalence_proof_lower_n(a,b,31);
    equivalence_proof_msb(a,b,31);
}




// #[verifier(bit_vector)]
// proof fn equivalence_proof_bv(a:u32, b:u32) 
//     requires        
//         forall|i: u32| #![auto]
//             i < 32 ==> (get_bit!(a, i) == get_bit!(b, i)),
//     ensures
//         a == b,
// {}


} // verus!
