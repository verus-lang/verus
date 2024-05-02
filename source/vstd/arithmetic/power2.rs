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
use crate::arithmetic::power::{
    pow,
    lemma_pow_positive,
    group_pow_properties,
    lemma_pow_adds,
    lemma_pow_strictly_increases,
};
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

/// Proof that `2^(e1 + e2)` is equivalent to `2^e1 * 2^e2`.
pub proof fn lemma_pow2_adds(e1: nat, e2: nat)
    ensures
        pow2(e1 + e2) == pow2(e1) * pow2(e2),
{
    lemma_pow2(e1);
    lemma_pow2(e2);
    lemma_pow2(e1 + e2);
    lemma_pow_adds(2, e1, e2);
}

/// Proof that `2^(e1 + e2)` is equivalent to `2^e1 * 2^e2` for all exponents `e1`, `e2`.
pub proof fn lemma_pow2_adds_auto()
    ensures
        forall|e1: nat, e2: nat| #[trigger] pow2(e1 + e2) == pow2(e1) * pow2(e2),
{
    assert forall|e1: nat, e2: nat| #[trigger] pow2(e1 + e2) == pow2(e1) * pow2(e2) by {
        lemma_pow2_adds(e1, e2);
    }
}

/// Proof that if `e1 < e2` then `2^e1 < 2^e2` for given `e1`, `e2`.
pub proof fn lemma_pow2_strictly_increases(e1: nat, e2: nat)
    requires
        e1 < e2,
    ensures
        pow2(e1) < pow2(e2),
{
    lemma_pow2(e1);
    lemma_pow2(e2);
    lemma_pow_strictly_increases(2, e1, e2);
}

/// Proof that if `e1 < e2` then `2^e1 < 2^e2` for all `e1`, `e2`.
pub proof fn lemma_pow2_strictly_increases_auto()
    ensures
        forall|e1: nat, e2: nat| e1 < e2 ==> #[trigger] pow2(e1) < #[trigger] pow2(e2),
{
    assert forall|e1: nat, e2: nat| e1 < e2 implies #[trigger] pow2(e1) < #[trigger] pow2(e2) by {
        lemma_pow2_strictly_increases(e1, e2);
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
        broadcast use group_pow_properties;

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
    assert forall|e: nat| 0 < e implies (#[trigger] (pow2(e)) - 1) / 2 == pow2((e - 1) as nat)
        - 1 by {
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

/// Mask with low n bits set.
pub open spec fn low_bits_mask(n: nat) -> nat {
    (pow2(n) - 1) as nat
}

/// Proof establishing the concrete values of all masks of bit sizes from 0 to
/// 64.
pub proof fn lemma_low_bits_mask_values_to64()
    ensures
        low_bits_mask(0) == 0x0,
        low_bits_mask(1) == 0x1,
        low_bits_mask(2) == 0x3,
        low_bits_mask(3) == 0x7,
        low_bits_mask(4) == 0xf,
        low_bits_mask(5) == 0x1f,
        low_bits_mask(6) == 0x3f,
        low_bits_mask(7) == 0x7f,
        low_bits_mask(8) == 0xff,
        low_bits_mask(9) == 0x1ff,
        low_bits_mask(10) == 0x3ff,
        low_bits_mask(11) == 0x7ff,
        low_bits_mask(12) == 0xfff,
        low_bits_mask(13) == 0x1fff,
        low_bits_mask(14) == 0x3fff,
        low_bits_mask(15) == 0x7fff,
        low_bits_mask(16) == 0xffff,
        low_bits_mask(17) == 0x1ffff,
        low_bits_mask(18) == 0x3ffff,
        low_bits_mask(19) == 0x7ffff,
        low_bits_mask(20) == 0xfffff,
        low_bits_mask(21) == 0x1fffff,
        low_bits_mask(22) == 0x3fffff,
        low_bits_mask(23) == 0x7fffff,
        low_bits_mask(24) == 0xffffff,
        low_bits_mask(25) == 0x1ffffff,
        low_bits_mask(26) == 0x3ffffff,
        low_bits_mask(27) == 0x7ffffff,
        low_bits_mask(28) == 0xfffffff,
        low_bits_mask(29) == 0x1fffffff,
        low_bits_mask(30) == 0x3fffffff,
        low_bits_mask(31) == 0x7fffffff,
        low_bits_mask(32) == 0xffffffff,
        low_bits_mask(33) == 0x1ffffffff,
        low_bits_mask(34) == 0x3ffffffff,
        low_bits_mask(35) == 0x7ffffffff,
        low_bits_mask(36) == 0xfffffffff,
        low_bits_mask(37) == 0x1fffffffff,
        low_bits_mask(38) == 0x3fffffffff,
        low_bits_mask(39) == 0x7fffffffff,
        low_bits_mask(40) == 0xffffffffff,
        low_bits_mask(41) == 0x1ffffffffff,
        low_bits_mask(42) == 0x3ffffffffff,
        low_bits_mask(43) == 0x7ffffffffff,
        low_bits_mask(44) == 0xfffffffffff,
        low_bits_mask(45) == 0x1fffffffffff,
        low_bits_mask(46) == 0x3fffffffffff,
        low_bits_mask(47) == 0x7fffffffffff,
        low_bits_mask(48) == 0xffffffffffff,
        low_bits_mask(49) == 0x1ffffffffffff,
        low_bits_mask(50) == 0x3ffffffffffff,
        low_bits_mask(51) == 0x7ffffffffffff,
        low_bits_mask(52) == 0xfffffffffffff,
        low_bits_mask(53) == 0x1fffffffffffff,
        low_bits_mask(54) == 0x3fffffffffffff,
        low_bits_mask(55) == 0x7fffffffffffff,
        low_bits_mask(56) == 0xffffffffffffff,
        low_bits_mask(57) == 0x1ffffffffffffff,
        low_bits_mask(58) == 0x3ffffffffffffff,
        low_bits_mask(59) == 0x7ffffffffffffff,
        low_bits_mask(60) == 0xfffffffffffffff,
        low_bits_mask(61) == 0x1fffffffffffffff,
        low_bits_mask(62) == 0x3fffffffffffffff,
        low_bits_mask(63) == 0x7fffffffffffffff,
        low_bits_mask(64) == 0xffffffffffffffff,
{
    reveal(pow2);
    #[verusfmt::skip]
    assert(
        low_bits_mask(0) == 0x0 &&
        low_bits_mask(1) == 0x1 &&
        low_bits_mask(2) == 0x3 &&
        low_bits_mask(3) == 0x7 &&
        low_bits_mask(4) == 0xf &&
        low_bits_mask(5) == 0x1f &&
        low_bits_mask(6) == 0x3f &&
        low_bits_mask(7) == 0x7f &&
        low_bits_mask(8) == 0xff &&
        low_bits_mask(9) == 0x1ff &&
        low_bits_mask(10) == 0x3ff &&
        low_bits_mask(11) == 0x7ff &&
        low_bits_mask(12) == 0xfff &&
        low_bits_mask(13) == 0x1fff &&
        low_bits_mask(14) == 0x3fff &&
        low_bits_mask(15) == 0x7fff &&
        low_bits_mask(16) == 0xffff &&
        low_bits_mask(17) == 0x1ffff &&
        low_bits_mask(18) == 0x3ffff &&
        low_bits_mask(19) == 0x7ffff &&
        low_bits_mask(20) == 0xfffff &&
        low_bits_mask(21) == 0x1fffff &&
        low_bits_mask(22) == 0x3fffff &&
        low_bits_mask(23) == 0x7fffff &&
        low_bits_mask(24) == 0xffffff &&
        low_bits_mask(25) == 0x1ffffff &&
        low_bits_mask(26) == 0x3ffffff &&
        low_bits_mask(27) == 0x7ffffff &&
        low_bits_mask(28) == 0xfffffff &&
        low_bits_mask(29) == 0x1fffffff &&
        low_bits_mask(30) == 0x3fffffff &&
        low_bits_mask(31) == 0x7fffffff &&
        low_bits_mask(32) == 0xffffffff &&
        low_bits_mask(33) == 0x1ffffffff &&
        low_bits_mask(34) == 0x3ffffffff &&
        low_bits_mask(35) == 0x7ffffffff &&
        low_bits_mask(36) == 0xfffffffff &&
        low_bits_mask(37) == 0x1fffffffff &&
        low_bits_mask(38) == 0x3fffffffff &&
        low_bits_mask(39) == 0x7fffffffff &&
        low_bits_mask(40) == 0xffffffffff &&
        low_bits_mask(41) == 0x1ffffffffff &&
        low_bits_mask(42) == 0x3ffffffffff &&
        low_bits_mask(43) == 0x7ffffffffff &&
        low_bits_mask(44) == 0xfffffffffff &&
        low_bits_mask(45) == 0x1fffffffffff &&
        low_bits_mask(46) == 0x3fffffffffff &&
        low_bits_mask(47) == 0x7fffffffffff &&
        low_bits_mask(48) == 0xffffffffffff &&
        low_bits_mask(49) == 0x1ffffffffffff &&
        low_bits_mask(50) == 0x3ffffffffffff &&
        low_bits_mask(51) == 0x7ffffffffffff &&
        low_bits_mask(52) == 0xfffffffffffff &&
        low_bits_mask(53) == 0x1fffffffffffff &&
        low_bits_mask(54) == 0x3fffffffffffff &&
        low_bits_mask(55) == 0x7fffffffffffff &&
        low_bits_mask(56) == 0xffffffffffffff &&
        low_bits_mask(57) == 0x1ffffffffffffff &&
        low_bits_mask(58) == 0x3ffffffffffffff &&
        low_bits_mask(59) == 0x7ffffffffffffff &&
        low_bits_mask(60) == 0xfffffffffffffff &&
        low_bits_mask(61) == 0x1fffffffffffffff &&
        low_bits_mask(62) == 0x3fffffffffffffff &&
        low_bits_mask(63) == 0x7fffffffffffffff &&
        low_bits_mask(64) == 0xffffffffffffffff
    ) by (compute_only);
}

} // verus!
