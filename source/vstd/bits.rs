//! Properties of bitwise operators.

use builtin::*;
use builtin_macros::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arithmetic::power2::{pow2, lemma_pow2_adds, lemma_pow2_pos, lemma2_to64};
#[cfg(verus_keep_ghost)]
use crate::arithmetic::div_mod::lemma_div_denominator;
#[cfg(verus_keep_ghost)]
use crate::calc_macro::*;

/// Proof that shift right by n is equivalent to division by 2^n.
proof fn lemma_u64_shr_is_div(x: u64, shift: u64)
    requires 0 <= shift < 64,
    ensures x >> shift == x as nat / pow2(shift as nat),
    decreases shift,
{
    reveal(pow2);
    if shift == 0 {
        assert(x >> 0 == x) by (bit_vector);
        assert(pow2(0) == 1) by (compute_only);
    } else {
        assert(x >> shift == (x >> ((sub(shift, 1)) as u64)) / 2) by (bit_vector)
            requires 0 < shift < 64;

        assert(x as nat / pow2(shift as nat) == (x as nat / (pow2((shift - 1) as nat) * pow2(1)))) by {
            lemma_pow2_adds((shift - 1) as nat, 1);
        }
        assert(x as nat / pow2(shift as nat) == (x as nat / pow2((shift - 1) as nat)) / 2) by {
            lemma_pow2_pos((shift - 1) as nat);
            lemma2_to64();
            lemma_div_denominator(x as int, pow2((shift - 1) as nat) as int, 2);
        }

        calc!{ (==)
            (x >> shift) as nat;
                {}
            ((x >> ((sub(shift, 1)) as u64)) / 2) as nat;
                { lemma_u64_shr_is_div(x, (shift - 1) as u64); }
            (x as nat / pow2((shift - 1) as nat)) / 2;
                {}
            x as nat / pow2(shift as nat);
        }
    }
}

}
