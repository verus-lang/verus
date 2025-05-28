// lemma originally from @hayley-leblanc
use builtin::*;
use builtin_macros::*;
use vstd::*;

verus! {

pub proof fn lemma_mod_subtract_helper(
    x: int,
    y: int,
    d: int,
    small_x: int,
    small_y: int,
    tmp1: int,
)
    by (integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (x + y) % d,
    ensures
        (small_x + y - tmp1) % d == 0,
{
}

pub proof fn lemma_mod_subtract(x: int, y: int, d: int)
    by (nonlinear_arith)
    requires
        d > 0,
        (x % d) + y >= d,
        0 <= y < d,
    ensures
        (x % d) + y - d == (x + y) % d,
{
    let small_x = x % d;
    let small_y = y % d;
    let tmp1 = (x + y) % d;
    lemma_mod_subtract_helper(x, y, d, small_x, small_y, tmp1);
}

pub proof fn lemma_mod_difference_equal_helper(
    x: int,
    y: int,
    d: int,
    small_x: int,
    small_y: int,
    tmp1: int,
    tmp2: int,
)
    by (integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (small_y - small_x) % d,
        tmp2 == (y - x) % d,
    ensures
        (tmp1 - tmp2) % d == 0,
{
}

pub proof fn lemma_mod_difference_equal(x: int, y: int, d: int)
    by (nonlinear_arith)
    requires
        d > 0,
        x <= y,
        x % d <= y % d,
        y - x < d,
    ensures
        y % d - x % d == y - x,
{
    let small_x = x % d;
    let small_y = y % d;
    let tmp1 = (small_y - small_x) % d;
    let tmp2 = (y - x) % d;
    lemma_mod_difference_equal_helper(x, y, d, small_x, small_y, tmp1, tmp2);
}

pub proof fn lemma_mod_wrapped_len_helper(
    x: int,
    y: int,
    d: int,
    small_x: int,
    small_y: int,
    tmp1: int,
)
    by (integer_ring)
    requires
        small_x == x % d,
        small_y == y % d,
        tmp1 == (d - small_x + small_y) % d,
    ensures
        (y - x - tmp1) % d == 0,
{
}

pub proof fn lemma_mod_wrapped_len(x: int, y: int, d: int)
    by (nonlinear_arith)
    requires
        d > 0,
        x <= y,
        x % d > y % d,
        y - x < d,
    ensures
        d - (x % d) + (y % d) == y - x,
{
    let small_x = x % d;
    let small_y = y % d;
    let tmp1 = (d - small_x + small_y) % d;
    lemma_mod_wrapped_len_helper(x, y, d, small_x, small_y, tmp1);
}

pub proof fn lemma_mod_between_helper(x: int, y: int, d: int)
    by (integer_ring)
    ensures
        (x % d - y % d) % d == (x - y) % d,
{
}

// note that below two facts are from the helper function, and the rest are done by this following function.
// x % d - y % d == x - y  mod d
// y % d - z % d == y - z  mod d
pub proof fn lemma_mod_between(d: int, x: int, y: int, z: int)
    by (nonlinear_arith)
    requires
        d > 0,
        x % d < y % d,
        y - x <= d,
        x <= z < y,
    ensures
        x % d <= z % d < y % d,
{
    lemma_mod_between_helper(x, z, d);
    lemma_mod_between_helper(y, z, d);
}

// TODO: with the new, stable approach to AIR variable naming, this lemma now times out
//       it is likely it was already unstable, and the new naming triggered the instability
// note that below two facts are from the helper function, and the rest are done by this following function.
// x % d - y % d == x - y  mod d
// y % d - z % d == y - z  mod d
pub proof fn lemma_mod_not_between(d: int, x: int, y: int, z: int)
    by (nonlinear_arith)
    requires
        d > 0,
        y % d < x % d,
        y - x <= d,
        x <= z < y,
    ensures
        z % d < y % d || z % d >= x % d,
{
    lemma_mod_between_helper(x, z, d);
    lemma_mod_between_helper(z, y, d);
}

fn main() {
}

} // verus!
