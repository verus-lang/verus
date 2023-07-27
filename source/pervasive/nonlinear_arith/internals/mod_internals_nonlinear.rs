#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::calc_macro::*;

verus! {

pub open spec fn modulus (x: int, y: int) -> int
{
    x % y
}

/* the remainder 0 divided by an integer is 0 */
// #[verifier::spinoff_prover]
proof fn lemma_mod_of_zero_is_zero(m:int)
    requires (0 as int) < m
    ensures   0 as int % m == 0 as int
{}

/* describes fundamentals of the modulus operator */
#[verifier(nonlinear)]
pub proof fn lemma_fundamental_div_mod(x:int, d:int)
    requires d != 0
    ensures  x == d * (x / d) + (x % d)
{}

/* the remained of 0 divided by any integer is always 0 */
// #[verifier::spinoff_prover]
proof fn lemma_0_mod_any()
    ensures forall |m: int| m > 0 ==> #[trigger] modulus(0, m) == 0
{}

/* a natural number x divided by a larger natural number gives a remainder equal to x */
#[verifier(nonlinear)]
pub proof fn lemma_small_mod(x:nat, m:nat)
    requires 
        x < m,
        0 < m
    ensures 
        #[trigger] modulus(x as int, m as int) == x as int
{}

/* the range of the modulus of any integer will be [0, m) where m is the divisor */
// Euclid's division lemma?
#[verifier(nonlinear)]
pub proof fn lemma_mod_range(x:int, m:int)
    requires m > 0
    ensures  0 <= #[trigger] modulus(x, m) < m
{}

}