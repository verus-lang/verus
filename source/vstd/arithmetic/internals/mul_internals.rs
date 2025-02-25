//! This file contains proofs related to multiplication. These are
//! internal functions used within the math standard library.
//!
//! It's based on the following file from the Dafny math standard library:
//! `Source/DafnyStandardLibraries/src/Std/Arithmetic/Internal/MulInternals.dfy`.
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

#[cfg(verus_keep_ghost)]
use super::super::super::arithmetic::internals::general_internals::{
    is_le, lemma_induction_helper,
};
use super::super::super::arithmetic::internals::mul_internals_nonlinear as MulINL;
#[cfg(verus_keep_ghost)]
use super::super::super::math::{add as add1, sub as sub1};

verus! {

/// This function performs multiplication recursively. It's only valid
/// when `x` is non-negative.
#[verifier::opaque]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends
        x >= 0,
    decreases x,
{
    if x <= 0 {
        0
    } else {
        y + mul_pos(x - 1, y)
    }
}

/// This function performs multiplication recursively.
pub open spec fn mul_recursive(x: int, y: int) -> int {
    if x >= 0 {
        mul_pos(x, y)
    } else {
        -1 * mul_pos(-1 * x, y)
    }
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate, proves the
/// predicate holds in the base case of 0, and proves correctness of
/// inductive steps both upward and downward from the base case. This
/// lemma invokes induction to establish that the predicate holds for
/// all integers.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i >= 0`, `f(i) ==> f(add1(i, 1))`.
/// `add1(i, 1)` is just `i + 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i <= 0`, `f(i) ==> f(sub1(i, 1))`.
/// `sub1(i, 1)` is just `i - 1`, but written in a functional style
/// so that it can be used where functional triggers are required.
pub proof fn lemma_mul_induction(f: spec_fn(int) -> bool)
    requires
        f(0),
        forall|i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
        forall|i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
    ensures
        forall|i: int| #[trigger] f(i),
{
    assert forall|i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// Proof that multiplication is always commutative
pub broadcast proof fn lemma_mul_commutes(x: int, y: int)
    ensures
        #[trigger] (x * y) == y * x,
{
}

/// Proof that multiplication distributes over addition by 1 and
/// over subtraction by 1
proof fn lemma_mul_successor()
    ensures
        forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall|x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y by {
        MulINL::lemma_mul_is_distributive_add(y, x, 1);
    }
    assert forall|x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y by {
        assert((x - 1) * y == y * (x - 1));
        MulINL::lemma_mul_is_distributive_add(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}

/// Proof that multiplication distributes over addition and over
/// subtraction
#[verifier::spinoff_prover]
pub broadcast proof fn lemma_mul_distributes_plus(x: int, y: int, z: int)
    ensures
        #[trigger] ((x + y) * z) == (x * z + y * z),
{
    lemma_mul_successor();
    assert forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z) by {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall|i: int| i >= 0 && #[trigger] f1(i) implies #[trigger] f1(add1(i, 1)) by {
            assert((x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f1(i) implies #[trigger] f1(sub1(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));
    }
}

#[verifier::spinoff_prover]
pub broadcast proof fn lemma_mul_distributes_minus(x: int, y: int, z: int)
    ensures
        #[trigger] ((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();
    assert forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall|i: int| i >= 0 && #[trigger] f2(i) implies #[trigger] f2(add1(i, 1)) by {
            assert((x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);
        };
        assert forall|i: int| i <= 0 && #[trigger] f2(i) implies #[trigger] f2(sub1(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };
        lemma_mul_induction(f2);
        assert(f2(y));
    }
}

/// This function expresses that multiplication is commutative,
/// distributes over addition, and distributes over subtraction
pub open spec fn mul_auto() -> bool {
    &&& forall|x: int, y: int| #[trigger] (x * y) == (y * x)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x + y) * z) == (x * z + y * z)
    &&& forall|x: int, y: int, z: int| #[trigger] ((x - y) * z) == (x * z - y * z)
}

pub broadcast group group_mul_properties_internal {
    lemma_mul_commutes,
    lemma_mul_distributes_plus,
    lemma_mul_distributes_minus,
}

// Check that the group_mul_properties_internal broadcast group group_provides the same properties as the _auto lemma it replaces
proof fn lemma_mul_properties_internal_prove_mul_auto()
    ensures
        mul_auto(),
{
    broadcast use group_mul_properties_internal;

    assert(mul_auto());
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate `f`, proves
/// the predicate holds in the base case of 0, and proves correctness
/// of inductive steps both upward and downward from the base case.
/// This lemma invokes induction to establish that the predicate holds
/// for the given integer `x`.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i`, `is_le(0, i)` implies `f(i) ==>
/// f(i + 1)`.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i`, `is_le(i, 0)` implies `f(i) ==>
/// f(i - 1)`.
pub proof fn lemma_mul_induction_auto(x: int, f: spec_fn(int) -> bool)
    requires
        mul_auto() ==> {
            &&& f(0)
            &&& (forall|i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
            &&& (forall|i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))
        },
    ensures
        mul_auto(),
        f(x),
{
    broadcast use group_mul_properties_internal;

    assert(forall|i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert(forall|i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

/// This utility function helps prove a mathematical property by
/// induction. The caller supplies an integer predicate `f`, proves
/// the predicate holds in the base case of 0, and proves correctness
/// of inductive steps both upward and downward from the base case.
/// This lemma invokes induction to establish that the predicate holds
/// for all integers.
///
/// To prove inductive steps upward from the base case, the caller
/// must establish that, for any `i`, `is_le(0, i)` implies `f(i) ==>
/// f(i + 1)`.
///
/// To prove inductive steps downward from the base case, the caller
/// must establish that, for any `i`, `is_le(i, 0)` implies `f(i) ==>
/// f(i - 1)`.
pub proof fn lemma_mul_induction_auto_forall(f: spec_fn(int) -> bool)
    requires
        mul_auto() ==> {
            &&& f(0)
            &&& (forall|i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
            &&& (forall|i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))
        },
    ensures
        mul_auto(),
        forall|i| #[trigger] f(i),
{
    assert(mul_auto()) by {
        lemma_mul_induction_auto(0, f);
    }
    assert forall|i| #[trigger] f(i) by {
        lemma_mul_induction_auto(i, f);
    }
}

} // verus!
