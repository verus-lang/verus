#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;

// IMO 1988, #6.
// Let a and b be positive integers such that (a^2 + b^2) / (ab + 1) is an integer.
// Prove that it is a perfect square.
//
// This is a classic example of "vieta jumping". It makes a decent exercise
// utilizing nonlinear arithmetic in Verus.
// Closely following the solution given here:
//    https://en.wikipedia.org/wiki/Vieta_jumping#Geometric_interpretation

verus! {

proof fn vieta_jump(b: int, c: int, x: int)
    by (nonlinear_arith)
    requires
        x * x - b * x + c == 0,
    ensures
        ({
            let y = b - x;
            y * y - b * y + c == 0 && y * x == c
        }),
{
}

proof fn sqrt2_contradiction(a: int)
    requires
        a * a == 2,
    ensures
        false,
{
    assert(a * a == 2 ==> false) by (nonlinear_arith);
}

proof fn is_perfect_square_wlog(a: int, b: int, q: int) -> (sqrt: int)
    requires
        a >= 0,
        b >= 0,
        a * a + b * b == (a * b + 1) * q,
        q > 2,
        a < b,
    ensures
        sqrt * sqrt == q,
    decreases a + b, 0int,
{
    if a == 0 {
        assert(a * a == 0);
        assert(a * b == 0);
        return b;
    } else {
        assert(b * b - (q * a) * b + (a * a - q) == 0) by {
            assert((a * b + 1) * q == (a * b) * q + q) by (nonlinear_arith);
            assert((a * b) * q == (q * a) * b) by (nonlinear_arith);
        }
        vieta_jump(q * a, a * a - q, b);
        let b1 = q * a - b;
        assert(b1 * b1 - (q * a) * b1 + (a * a - q) == 0);
        assert(a * a + b1 * b1 == (a * b1 + 1) * q) by {
            assert((a * b1 + 1) * q == (a * b1) * q + q) by (nonlinear_arith);
            assert((a * b1) * q == (q * a) * b1) by (nonlinear_arith);
        }
        assert(b1 < b) by {
            assert(a > 0);
            assert(b1 * b == a * a - q);
            assert(b1 <= a) by {
                assert(a >= 0 && b >= 0 && b1 > a && b > a ==> b1 * b >= a * a)
                    by (nonlinear_arith);
            }
        }
        assert(b1 >= 0) by {
            assert(a * a + b1 * b1 == (a * b1 + 1) * q && a >= 1 && q > 2 ==> a * b1 + 1 > 0)
                by (nonlinear_arith);
            assert(a * b1 + 1 > 0 && a > 0 ==> b1 >= 0) by (nonlinear_arith);
        }
        return is_perfect_square(a, b1, q);
    }
}

// Main result
proof fn is_perfect_square(a: int, b: int, q: int) -> (sqrt: int)
    requires
        a >= 0,
        b >= 0,
        a * a + b * b == (a * b + 1) * q,
    ensures
        sqrt * sqrt == q,
    decreases a + b, 1int,
{
    if q < 0 {
        assert(a >= 0 && b >= 0 && a * a + b * b == (a * b + 1) * q ==> q >= 0)
            by (nonlinear_arith);
        assert(false);
        return 0;
    } else if q == 0 {
        return 0;
    } else if q == 1 {
        return 1;
    } else if q == 2 {
        assert((a - b) * (a - b) == 2) by (nonlinear_arith)
            requires
                a * a + b * b == (a * b + 1) * 2,
        ;
        sqrt2_contradiction(a - b);
        return 0;
    } else {
        assert(q > 2);
        if a == b {
            assert(2 * a * a == a * a + a * a) by (nonlinear_arith);
            assert(q > 2 ==> (a * a + 1) * q >= (a * a + 1) * 2) by (nonlinear_arith);
            assert(false);
            return 0;
        } else if a < b {
            return is_perfect_square_wlog(a, b, q);
        } else {
            assert(a > b);
            return is_perfect_square_wlog(b, a, q);
        }
    }
}

fn main() {
}

} // verus!
