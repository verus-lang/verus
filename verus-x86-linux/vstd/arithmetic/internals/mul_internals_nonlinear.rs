//! This file contains proofs related to multiplication that require
//! nonlinear-arithmetic reasoning to prove. These are internal
//! functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/MulInternalsNonlinear.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT
//! *******************************************************************************/
/*
   WARNING: Think three times before adding to this file, as nonlinear
   verification is highly unstable!
*/
// may be try to use singular?
#[allow(unused_imports)]
use super::super::super::prelude::*;

verus! {

/// Proof that multiplying two positive integers `x` and `y` will result in a positive integer
#[verifier::nonlinear]
pub proof fn lemma_mul_strictly_positive(x: int, y: int)
    ensures
        (0 < x && 0 < y) ==> (0 < x * y),
{
}

/// Proof that `x` and `y` are both nonzero if and only if `x * y` is nonzero
#[verifier::nonlinear]
pub proof fn lemma_mul_nonzero(x: int, y: int)
    ensures
        x * y != 0 <==> x != 0 && y != 0,
{
}

/// Proof that multiplication is associative in this specific case,
/// i.e., that `x * y * z` is the same no matter which of the two
/// multiplications is done first
#[verifier::nonlinear]
pub proof fn lemma_mul_is_associative(x: int, y: int, z: int)
    ensures
        x * (y * z) == (x * y) * z,
{
}

/// Proof that multiplication distributes over addition in this
/// specific case, i.e., that `x * (y + z)` equals `x * y` plus `x * z`
#[verifier::nonlinear]
pub proof fn lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures
        x * (y + z) == x * y + x * z,
{
}

/// Proof that the if the product of two nonzero integers `x` and `y`
/// is nonnegative, then it's greater than or equal to each of `x` and
/// `y`
#[verifier::nonlinear]
pub proof fn lemma_mul_ordering(x: int, y: int)
    requires
        x != 0,
        y != 0,
        0 <= x * y,
    ensures
        x * y >= x && x * y >= y,
{
}

/// Proof that multiplying by a positive integer preserves inequality
/// in this specific case, i.e., that since `x < y` and `z > 0` we can
/// conclude that `x * z < y * z`.
#[verifier::nonlinear]
pub proof fn lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires
        x < y,
        z > 0,
    ensures
        x * z < y * z,
{
}

} // verus!
