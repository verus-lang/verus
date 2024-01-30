#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;

use crate::nonlinear_arith::internals::general_internals::{is_le, lemma_induction_helper};
use crate::nonlinear_arith::internals::mul_internals_nonlinear as MulINL;
use crate::nonlinear_arith::math::{add as add1, sub as sub1};

verus! {

/// performs multiplication for positive integers using recursive addition
/// change x to nat?
// NEED TO ASK, here, we either change x into nat or return 0 when x < 0
// This is because we do not have partial functions
// and the recommend clause is too weak so that we actually need to consider
// the x < 0 case
#[verifier(opaque)]
pub open spec fn mul_pos(x: int, y: int) -> int
    recommends x >= 0
    decreases x
    // any design reason for using recommends instead of requires?
{
    if x <= 0 {
        0 
    } else {
        y + mul_pos(x - 1, y) 
    }
}

/// performs multiplication for both positive and negative integers
pub open spec fn mul_recursive(x: int, y: int) -> int
{
    if x >= 0 { mul_pos(x, y) }
    else { -1 * mul_pos(-1 * x, y) }
}

/// performs induction on multiplication
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_induction(f: FnSpec(int) -> bool)
    requires 
        f(0),
        forall |i: int| i >= 0 && #[trigger] f(i) ==> #[trigger] f(add1(i, 1)),
        forall |i: int| i <= 0 && #[trigger] f(i) ==> #[trigger] f(sub1(i, 1)),
    ensures
        forall |i: int| #[trigger] f(i)
{
    assert forall |i: int| #[trigger] f(i) by { lemma_induction_helper(1, f, i) };
}

/// proves that multiplication is always commutative
// #[verifier::spinoff_prover]
proof fn lemma_mul_commutes()
    ensures 
        forall |x: int, y: int| #[trigger](x * y) == y * x
{}

/// proves the distributive property of multiplication when multiplying an interger
/// by (x +/- 1)
// #[verifier::spinoff_prover]
proof fn lemma_mul_successor()
    ensures 
        forall |x: int, y: int| #[trigger] ((x + 1) * y) == x * y + y,
        forall |x: int, y: int| #[trigger] ((x - 1) * y) == x * y - y,
{
    assert forall |x:int, y:int| #[trigger]((x + 1) * y) == x * y + y by {
        MulINL::lemma_mul_is_distributive_add(y, x, 1);
    }
    
    assert forall |x:int, y:int| #[trigger]((x - 1) * y) == x * y - y by {
        assert((x - 1) * y  == y * (x - 1));
        MulINL::lemma_mul_is_distributive_add(y, x, -1);
        assert(y * (x - 1) == y * x + y * -1);
        assert(-1 * y == -y);
        assert(x * y + (-1 * y) == x * y - y);
    }
}

/// proves the distributive property of multiplication
#[verifier(spinoff_prover)]
proof fn lemma_mul_distributes()
    ensures
    forall |x: int, y: int, z: int| #[trigger]((x + y) * z) == (x * z + y * z),
    forall |x: int, y: int, z: int| #[trigger]((x - y) * z) == (x * z - y * z),
{
    lemma_mul_successor();

    assert forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
        by
    {
        let f1 = |i: int| ((x + i) * z) == (x * z + i * z);
        assert(f1(0));
        assert forall |i: int| i >= 0 && #[trigger] f1(i) implies #[trigger]f1(add1(i, 1)) by {
            assert(  (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f1(i) implies #[trigger]f1(sub1(i, 1)) by {
            assert((x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z);
        };
        lemma_mul_induction(f1);
        assert(f1(y));


    }

    assert forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z) by {
        let f2 = |i: int| ((x - i) * z) == (x * z - i * z);
        assert(f2(0));
        assert forall |i: int| i >= 0 && #[trigger] f2(i) implies #[trigger]f2(add1(i, 1)) by {
            assert(  (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z);

        };
        assert forall |i: int| i <= 0 && #[trigger] f2(i) implies #[trigger]f2(sub1(i, 1)) by {
            assert((x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z);
        };

        lemma_mul_induction(f2);
        assert(f2(y));
    }

}

/// groups distributive and associative properties of multiplication
// #[verifier::spinoff_prover]
pub open spec fn mul_auto() -> bool
{
    &&& forall |x:int, y:int| #[trigger](x * y) == (y * x)
    &&& forall |x:int, y:int, z:int| #[trigger]((x + y) * z) == (x * z + y * z)
    &&& forall |x:int, y:int, z:int| #[trigger]((x - y) * z) == (x * z - y * z)
}

/// proves that mul_auto is valid
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_auto()
    ensures  mul_auto()
{
    lemma_mul_distributes();
}

/// performs auto induction on multiplication for all i s.t. f(i) exists */
// #[verifier::spinoff_prover]
pub proof fn lemma_mul_induction_auto(x: int, f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        f(x),
{
    lemma_mul_auto();
    assert (forall |i| is_le(0, i) && #[trigger] f(i) ==> f(i + 1));
    assert (forall |i| is_le(i, 0) && #[trigger] f(i) ==> f(i - 1));
    lemma_mul_induction(f);
}

pub proof fn lemma_mul_induction_auto_forall(f: FnSpec(int) -> bool)
    requires mul_auto() ==> { &&&  f(0)
                              &&& (forall |i| #[trigger] is_le(0, i) && f(i) ==> f(i + 1))
                              &&& (forall |i| #[trigger] is_le(i, 0) && f(i) ==> f(i - 1))}
    ensures  
        mul_auto(),
        forall |i| #[trigger] f(i),
{
    assert(mul_auto()) by {
        lemma_mul_induction_auto(0, f);
    }
    assert forall |i| #[trigger] f(i) by {
        lemma_mul_induction_auto(i, f);
    }
}

}
