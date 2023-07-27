//! internals for the division

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

/* zero divided by an integer besides 0 is 0 */
#[verifier(nonlinear)]
pub proof fn lemma_div_of0(d: int)
    requires d != 0 as int
    ensures 0 as int / d == 0 as int
{}

/* the quotient of an integer divided by itself is 1 */
pub proof fn lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
{}

/* dividing a smaller integer by a larger integer results in a quotient of 0  */
#[verifier(nonlinear)]
pub proof fn lemma_small_div()
    ensures forall |x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger](x / d) == 0
{}

// TODO: how to translate the `real` type? 
//       seems to be only used here

/* the quotient of dividing a positive real number (not 0) by a smaller positive real number*/
// proof fn lemma_real_div_gt(x:real, y:real)
//     requires 
//         x > y,
//         x >= 0.0,
//         y > 0.0
//     ensures
//         x / y > 1 as real
// {}

}
