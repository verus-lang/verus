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
use super::super::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use super::power::{pow, lemma_pow_positive, lemma_pow_adds, lemma_pow_strictly_increases};

/// This function computes 2 to the power of the given natural number
/// `e`. It's opaque so that the SMT solver doesn't waste time
/// repeatedly recursively unfolding it.
#[verifier::opaque]
pub open spec fn pow2(e: nat) -> nat
    decreases
            e  // ensures pow2(e) > 0
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
pub broadcast proof fn lemma_pow2_pos(e: nat)
    ensures
        #[trigger] pow2(e) > 0,
{
    reveal(pow2);
    lemma_pow_positive(2, e);
}

/// Proof that `pow2(e)` is equivalent to `pow(2, e)`
pub broadcast proof fn lemma_pow2(e: nat)
    ensures
        #[trigger] pow2(e) == pow(2, e) as int,
    decreases e,
{
    reveal(pow);
    reveal(pow2);
    if e != 0 {
        lemma_pow2((e - 1) as nat);
    }
}

/// Proof relating 2^e to 2^(e-1).
pub broadcast proof fn lemma_pow2_unfold(e: nat)
    requires
        e > 0,
    ensures
        #[trigger] pow2(e) == 2 * pow2((e - 1) as nat),
{
    lemma_pow2(e);
    lemma_pow2((e - 1) as nat);
}

/// Proof that `2^(e1 + e2)` is equivalent to `2^e1 * 2^e2`.
pub broadcast proof fn lemma_pow2_adds(e1: nat, e2: nat)
    ensures
        #[trigger] pow2(e1 + e2) == pow2(e1) * pow2(e2),
{
    lemma_pow2(e1);
    lemma_pow2(e2);
    lemma_pow2(e1 + e2);
    lemma_pow_adds(2, e1, e2);
}

/// Proof that if `e1 < e2` then `2^e1 < 2^e2`.
pub broadcast proof fn lemma_pow2_strictly_increases(e1: nat, e2: nat)
    requires
        e1 < e2,
    ensures
        #[trigger] pow2(e1) < #[trigger] pow2(e2),
{
    lemma_pow2(e1);
    lemma_pow2(e2);
    lemma_pow_strictly_increases(2, e1, e2);
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
    #[verusfmt::skip]
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

} // verus!
