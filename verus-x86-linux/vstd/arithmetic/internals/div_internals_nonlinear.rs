//! This file contains proofs related to division that require
//! nonlinear-arithmetic reasoning to prove. These are internal
//! functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/DivInternalsNonlinear.dfy`.
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

/// Proof that 0 divided by any given integer `d` is 0
#[verifier::nonlinear]
pub proof fn lemma_div_of0(d: int)
    requires
        d != 0 as int,
    ensures
        0 as int / d == 0 as int,
{
}

/// Proof that any given integer `d` divided by itself is 1
pub proof fn lemma_div_by_self(d: int)
    requires
        d != 0,
    ensures
        d / d == 1,
{
}

/// Proof that dividing a non-negative integer by a larger integer results in a quotient of 0
#[verifier::nonlinear]
pub proof fn lemma_small_div()
    ensures
        forall|x: int, d: int| 0 <= x < d && d > 0 ==> #[trigger] (x / d) == 0,
{
}

} // verus!
