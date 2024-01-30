//! Lemmas for powerz of 2.

#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

use crate::nonlinear_arith::power::{pow, lemma_pow_positive, lemma_pow_auto}; 
use crate::nonlinear_arith::internals::mul_internals::lemma_mul_induction_auto; 
use crate::nonlinear_arith::internals::general_internals::is_le; 

#[verifier(opaque)]
pub open spec fn pow2(e: nat) -> nat
    decreases e
    // ensures pow2(e) > 0  
    // cannot have ensurs clause in spec functions
    // a workaround is the lemma_pow2_pos below
{
    // you cannot reveal in a spec function, which cause more reveals clauses
    // for the proof
    // reveal(pow);
    pow(2, e) as nat
}

/// 2 to the power of any natural number will always be positive
// #[verifier::spinoff_prover]
pub proof fn lemma_pow2_pos(e: nat)
    ensures pow2(e) > 0
{
    reveal(pow2);
    lemma_pow_positive(2, e);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_pow2_pos_auto()
    ensures forall |e: nat| #[trigger]pow2(e) > 0
{
    assert forall |e: nat| #[trigger]pow2(e) > 0 by
    {
        lemma_pow2_pos(e);
    }
}

/// pow2() is equivalent to pow() with base 2.
// #[verifier::spinoff_prover]
pub proof fn lemma_pow2(e: nat)
    ensures pow2(e) == pow(2, e) as int
    decreases e
{
    reveal(pow);
    reveal(pow2);
    if e != 0 {
        lemma_pow2((e - 1) as nat);
    }
}

// #[verifier::spinoff_prover]
pub proof fn lemma_pow2_auto()
    ensures forall |e: nat| #[trigger]pow2(e) == pow(2, e)
{
    assert forall |e: nat| #[trigger]pow2(e) == pow(2, e) by
    {
    lemma_pow2(e);
    }
}

/// `(2^e - 1) / 2 = 2^(e - 1) - 1`
// #[verifier::spinoff_prover]
pub proof fn lemma_pow2_mask_div2(e: nat)
    requires 0 < e
    ensures (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1
{
    let f = |e: int| 0 < e ==> (pow2(e as nat) - 1) / 2 == pow2((e - 1) as nat) - 1;
    assert forall |i: int|  #[trigger]is_le(0, i) && f(i) implies f(i + 1) by {
        lemma_pow_auto();
        lemma_pow2_auto();
    };
    lemma_mul_induction_auto(e as int, f);
}

// #[verifier::spinoff_prover]
pub proof fn lemma_pow2_mask_div2_auto()
    ensures 
        forall |e: nat| #![trigger pow2(e)] 0 < e ==> (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1
{
    reveal(pow2);
    assert forall |e: nat| 0 < e implies (#[trigger](pow2(e)) - 1) / 2 == pow2((e - 1) as nat) - 1 by
    {
        lemma_pow2_mask_div2(e);
    }
}

/// Lays out the powers of 2 from 0 to 32 and also 2^64
// #[verifier::spinoff_prover]
pub proof fn lemma2_to64()
    ensures 
        pow2(0) == 0x1,
        pow2(1) == 0x2,
        pow2(2) == 0x4,
        pow2(3) == 0x8,
        pow2(4) == 0x10,
        pow2(5) == 0x20,
        pow2(6) == 0x40,
        pow2(7) == 0x80,
        pow2(8) == 0x100,
        pow2(9) == 0x200,
        pow2(10) == 0x400,
        pow2(11) == 0x800,
        pow2(12) == 0x1000,
        pow2(13) == 0x2000,
        pow2(14) == 0x4000,
        pow2(15) == 0x8000,
        pow2(16) == 0x10000,
        pow2(17) == 0x20000,
        pow2(18) == 0x40000,
        pow2(19) == 0x80000,
        pow2(20) == 0x100000,
        pow2(21) == 0x200000,
        pow2(22) == 0x400000,
        pow2(23) == 0x800000,
        pow2(24) == 0x1000000,
        pow2(25) == 0x2000000,
        pow2(26) == 0x4000000,
        pow2(27) == 0x8000000,
        pow2(28) == 0x10000000,
        pow2(29) == 0x20000000,
        pow2(30) == 0x40000000,
        pow2(31) == 0x80000000,
        pow2(32) == 0x100000000,
        pow2(64) == 0x10000000000000000,
{
    reveal(pow2);
    reveal(pow);
    assert(
        pow2(0) == 0x1 &&
        pow2(1) == 0x2 &&
        pow2(2) == 0x4 &&
        pow2(3) == 0x8 &&
        pow2(4) == 0x10 &&
        pow2(5) == 0x20 &&
        pow2(6) == 0x40 &&
        pow2(7) == 0x80 &&
        pow2(8) == 0x100 &&
        pow2(9) == 0x200 &&
        pow2(10) == 0x400 &&
        pow2(11) == 0x800 &&
        pow2(12) == 0x1000 &&
        pow2(13) == 0x2000 &&
        pow2(14) == 0x4000 &&
        pow2(15) == 0x8000 &&
        pow2(16) == 0x10000 &&
        pow2(17) == 0x20000 &&
        pow2(18) == 0x40000 &&
        pow2(19) == 0x80000 &&
        pow2(20) == 0x100000 &&
        pow2(21) == 0x200000 &&
        pow2(22) == 0x400000 &&
        pow2(23) == 0x800000 &&
        pow2(24) == 0x1000000 &&
        pow2(25) == 0x2000000 &&
        pow2(26) == 0x4000000 &&
        pow2(27) == 0x8000000 &&
        pow2(28) == 0x10000000 &&
        pow2(29) == 0x20000000 &&
        pow2(30) == 0x40000000 &&
        pow2(31) == 0x80000000 &&
        pow2(32) == 0x100000000 &&
        pow2(64) == 0x10000000000000000
    ) by(compute_only);
}

}
