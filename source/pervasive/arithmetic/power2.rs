//! This file contains proofs related to powers of 2. These are part
//! of the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Power2.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT
//! *******************************************************************************/
#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::power::{pow, lemma_pow_positive, lemma_pow_auto};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::mul_internals::lemma_mul_induction_auto;
#[cfg(verus_keep_ghost)]
use crate::arithmetic::internals::general_internals::is_le;

/// This function computes 2 to the power of the given natural number
/// `e`. It's opaque so that the SMT solver doesn't waste time
/// repeatedly recursively unfolding it.
#[verifier(opaque)]
pub open spec fn pow2(e: nat) -> nat
    decreases
            e// ensures pow2(e) > 0
            // cannot have ensurs clause in spec functions
            // a workaround is the lemma_pow2_pos below
            ,
{
    // you cannot reveal in a spec function, which cause more reveals clauses
    // for the proof
    // reveal(pow);
    pow(2, e) as nat
}

/// Proof that 2 to the power of any natural number (specifically,
/// `e`) is positive
pub proof fn lemma_pow2_pos(e: nat)
    ensures
        pow2(e) > 0,
{
    reveal(pow2);
    lemma_pow_positive(2, e);
}

/// Proof that 2 to the power of any natural number is positive
pub proof fn lemma_pow2_pos_auto()
    ensures
        forall|e: nat| #[trigger] pow2(e) > 0,
{
    assert forall|e: nat| #[trigger] pow2(e) > 0 by {
        lemma_pow2_pos(e);
    }
}

/// Proof that `pow2(e)` is equivalent to `pow(2, e)`
pub proof fn lemma_pow2(e: nat)
    ensures
        pow2(e) == pow(2, e) as int,
    decreases e,
{
    reveal(pow);
    reveal(pow2);
    if e != 0 {
        lemma_pow2((e - 1) as nat);
    }
}

/// Proof that `pow2(e)` is equivalent to `pow(2, e)` for all `e`
pub proof fn lemma_pow2_auto()
    ensures
        forall|e: nat| #[trigger] pow2(e) == pow(2, e),
{
    assert forall|e: nat| #[trigger] pow2(e) == pow(2, e) by {
        lemma_pow2(e);
    }
}

/// Proof that, for the given positive number `e`, `(2^e - 1) / 2 == 2^(e - 1) - 1`
pub proof fn lemma_pow2_mask_div2(e: nat)
    requires
        0 < e,
    ensures
        (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1,
{
    let f = |e: int| 0 < e ==> (pow2(e as nat) - 1) / 2 == pow2((e - 1) as nat) - 1;
    assert forall|i: int| #[trigger] is_le(0, i) && f(i) implies f(i + 1) by {
        lemma_pow_auto();
        lemma_pow2_auto();
    };
    lemma_mul_induction_auto(e as int, f);
}

/// Proof that, for any positive number `e`, `(2^e - 1) / 2 == 2^(e - 1) - 1`
pub proof fn lemma_pow2_mask_div2_auto()
    ensures
        forall|e: nat| #![trigger pow2(e)] 0 < e ==> (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1,
{
    reveal(pow2);
    assert forall|e: nat| 0 < e implies (#[trigger]
    (pow2(e)) - 1) / 2 == pow2((e - 1) as nat) - 1 by {
        lemma_pow2_mask_div2(e);
    }
}

/// Proof establishing the concrete values for all powers of 2 from 0 to 32 and also 2^64
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
    assert(pow2(0) == 0x1);
    assert(pow2(1) == 0x2);
    assert(pow2(2) == 0x4);
    assert(pow2(3) == 0x8);
    assert(pow2(4) == 0x10);
    assert(pow2(5) == 0x20);
    assert(pow2(6) == 0x40);
    assert(pow2(7) == 0x80);
    assert(pow2(8) == 0x100);
    assert(pow2(9) == 0x200);
    assert(pow2(10) == 0x400);
    assert(pow2(11) == 0x800);
    assert(pow2(12) == 0x1000);
    assert(pow2(13) == 0x2000);
    assert(pow2(14) == 0x4000);
    assert(pow2(15) == 0x8000);
    assert(pow2(16) == 0x10000);
    assert(pow2(17) == 0x20000);
    assert(pow2(18) == 0x40000);
    assert(pow2(19) == 0x80000);
    assert(pow2(20) == 0x100000);
    assert(pow2(21) == 0x200000);
    assert(pow2(22) == 0x400000);
    assert(pow2(23) == 0x800000);
    assert(pow2(24) == 0x1000000);
    assert(pow2(25) == 0x2000000);
    assert(pow2(26) == 0x4000000);
    assert(pow2(27) == 0x8000000);
    assert(pow2(28) == 0x10000000);
    assert(pow2(29) == 0x20000000);
    assert(pow2(30) == 0x40000000);
    assert(pow2(31) == 0x80000000);
    assert(pow2(32) == 0x100000000);
    assert(pow2(33) == 0x200000000);
    assert(pow2(34) == 0x400000000);
    assert(pow2(35) == 0x800000000);
    assert(pow2(36) == 0x1000000000);
    assert(pow2(37) == 0x2000000000);
    assert(pow2(38) == 0x4000000000);
    assert(pow2(39) == 0x8000000000);
    assert(pow2(40) == 0x10000000000);
    assert(pow2(41) == 0x20000000000);
    assert(pow2(42) == 0x40000000000);
    assert(pow2(43) == 0x80000000000);
    assert(pow2(44) == 0x100000000000);
    assert(pow2(45) == 0x200000000000);
    assert(pow2(46) == 0x400000000000);
    assert(pow2(47) == 0x800000000000);
    assert(pow2(48) == 0x1000000000000);
    assert(pow2(49) == 0x2000000000000);
    assert(pow2(50) == 0x4000000000000);
    assert(pow2(51) == 0x8000000000000);
    assert(pow2(52) == 0x10000000000000);
    assert(pow2(53) == 0x20000000000000);
    assert(pow2(54) == 0x40000000000000);
    assert(pow2(55) == 0x80000000000000);
    assert(pow2(56) == 0x100000000000000);
    assert(pow2(57) == 0x200000000000000);
    assert(pow2(58) == 0x400000000000000);
    assert(pow2(59) == 0x800000000000000);
    assert(pow2(60) == 0x1000000000000000);
    assert(pow2(61) == 0x2000000000000000);
    assert(pow2(62) == 0x4000000000000000);
    assert(pow2(63) == 0x8000000000000000);
    assert(pow2(64) == 0x10000000000000000);
    /*
       assert by compute isn't currently working for vstd, but when it is, the following will
       be the better approach:

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
    */
}

} // verus!
