//! This file contains proofs related to modulo that require
//! nonlinear-arithmetic reasoning to prove. These are internal
//! functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/ModInternalsNonlinear.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT
//! *******************************************************************************/
#[allow(unused_imports)]
use super::super::super::prelude::*;

verus! {

/// Computes `x % y`. This is useful where we want to trigger on a
/// modulo operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn modulus(x: int, y: int) -> int {
    x % y
}

/// Proof that 0 modulo any positive integer `m` is 0
proof fn lemma_mod_of_zero_is_zero(m: int)
    requires
        0 < m,
    ensures
        0 as int % m == 0 as int,
{
}

/// Proof of the fundamental theorem of division and modulo: That for
/// any positive divisor `d` and any integer `x`, `x` is equal to `d`
/// times `x / d` plus `x % d`.
#[verifier::nonlinear]
pub proof fn lemma_fundamental_div_mod(x: int, d: int)
    requires
        d != 0,
    ensures
        x == d * (x / d) + (x % d),
{
}

/// Proof that 0 modulo any integer is 0
proof fn lemma_0_mod_anything()
    ensures
        forall|m: int| m > 0 ==> #[trigger] modulus(0, m) == 0,
{
}

/// Proof that a natural number `x` divided by a larger natural number
/// `m` gives a remainder equal to `x`
#[verifier::nonlinear]
pub proof fn lemma_small_mod(x: nat, m: nat)
    requires
        x < m,
        0 < m,
    ensures
        #[trigger] modulus(x as int, m as int) == x as int,
{
}

/// Proof of Euclid's division lemma, i.e., that any integer `x`
/// modulo any positive integer `m` is in the half-open range `[0, m)`.
#[verifier::nonlinear]
pub proof fn lemma_mod_range(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= #[trigger] modulus(x, m) < m,
{
}

} // verus!
