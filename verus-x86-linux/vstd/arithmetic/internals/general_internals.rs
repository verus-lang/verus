//! This file contains general internal functions used within the math
//! standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/GeneralInternals.dfy`.
//! That file has the following copyright notice:
//! /*******************************************************************************
//! *  Original: Copyright (c) Microsoft Corporation
//! *  SPDX-License-Identifier: MIT
//! *
//! *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
//! *  SPDX-License-Identifier: MIT
//! *******************************************************************************/
//! Declares helper lemmas and predicates for non-linear arithmetic
#[cfg(verus_keep_ghost)]
use super::super::super::math::{add as add1, sub as sub1};
use super::super::super::prelude::*;

verus! {

/// Computes the boolean `x <= y`. This is useful where we want to
/// trigger on a `<=` operator but we need a functional rather than a
/// mathematical trigger. (A trigger must be fully functional or fully
/// mathematical.)
pub open spec fn is_le(x: int, y: int) -> bool {
    x <= y
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of nonnegative
/// values of `x`.
proof fn lemma_induction_helper_pos(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x >= 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases x,
{
    if (x >= n) {
        assert(x - n < x);
        lemma_induction_helper_pos(n, f, x - n);
        assert(f(add1(x - n, n)));
        assert(f((x - n) + n));
    }
}

/// This proof, local to this module, aids in the process of proving
/// [`lemma_induction_helper`] by covering only the case of negative
/// values of `x`.
proof fn lemma_induction_helper_neg(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        x < 0,
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
    decreases -x,
{
    if (-x <= n) {
        lemma_induction_helper_pos(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    } else {
        lemma_induction_helper_neg(n, f, x + n);
        assert(f(sub1(x + n, n)));
        assert(f((x + n) - n));
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in certain base cases, and proves correctness of
/// inductive steps both upward and downward from the base cases. This
/// lemma invokes induction to establish that the predicate holds for
/// the given arbitrary input `x`.
///
/// `f`: The integer predicate
///
/// `n`: Upper bound on the base cases. Specifically, the caller
/// establishes `f(i)` for every value `i` satisfying `0 <= i < n`.
///
/// `x`: The desired case established by this lemma. Its postcondition
/// is thus simply `f(x)`.
///
/// To prove inductive steps upward from the base cases, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, n))`.
/// `add1(i, n)` is just `i + n`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base cases, the caller
/// must establish that, for any `i < n`, `f(i) ==> f(sub1(i, n))`.
/// `sub1(i, n)` is just `i - n`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_induction_helper(n: int, f: spec_fn(int) -> bool, x: int)
    requires
        n > 0,
        forall|i: int| 0 <= i < n ==> #[trigger] f(i),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, n)),
        forall|i: int| i < n && #[trigger] f(i) ==> #[trigger] f(sub1(i, n)),
    ensures
        f(x),
{
    if (x >= 0) {
        lemma_induction_helper_pos(n, f, x);
    } else {
        lemma_induction_helper_neg(n, f, x);
    }
}

} // verus!
