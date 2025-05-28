// Some of the lemmas are ported from the following:
// https://github.com/dafny-lang/libraries/blob/master/src/NonlinearArithmetic/Power2.dfy
// https://github.com/dafny-lang/libraries/blob/master/src/NonlinearArithmetic/Power.dfy
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

#[verifier::bit_vector]
proof fn left_shift_by_one(bv: u32, e: u32)
    requires
        e > 0,
        e <= 32,
    ensures
        bv << e == (bv << sub(e, 1)) << 1u32,
    decreases e,
{
    // REVIEW:                 ^^^^^^^^^^ expected `u32`, found struct `builtin::int`
    // get this error when updated to new syntax. Type casting (i.e. `(e - 1u32) as u32`) does not make this error disappear
}

#[verifier::bit_vector]
proof fn left_shift_by_one_is_mul2(bv: u32, e: u32)
    requires
        e > 0,
        e <= 32,
        bv << e == (bv << sub(e, 1)) << 1,
    ensures
        (bv << e) == mul(2, bv << sub(e, 1)),
{
}

spec fn pow2(e: nat) -> nat
    decreases (e),
{
    if e == 0 {
        1
    } else {
        2 * pow2((e - 1) as nat)
    }
}

proof fn lemma_pow2_0()
    ensures
        pow2(0) == 1,
{
}

proof fn lemma_pow2_unfold3(e: nat)
    requires
        e > 3,
    ensures
        pow2(e) == pow2((e - 3) as nat) * 8,
{
    reveal_with_fuel(pow2, 3);
}

// (2^e - 1) / 2 = 2^(e - 1) - 1
proof fn lemma_pow2_make_div(e: nat)
    requires
        e > 0,
    ensures
        (pow2(e) - 1) / 2 == pow2((e - 1) as nat) - 1,
    decreases e,
{
    if e == 1 {
    } else {
        lemma_pow2_make_div((e - 1) as nat)
    }
}

proof fn lemma_pow2_2e(e: nat)
    requires
        e > 0,
    ensures
        (pow2(2 * e)) == 4 * pow2(2 * ((e - 1) as nat)),
    decreases e,
{
    reveal_with_fuel(pow2, 3);
    if e == 1 {
        assert(pow2(2) == 4);
    } else {
        lemma_pow2_2e((e - 1) as nat)
    }
}

#[verifier::nonlinear]
proof fn lemma_pow2_two_e(e: nat)
    requires
        e >= 0,
    ensures
        pow2(e) * pow2(e) == pow2(2 * e),
    decreases e,
{
    if e != 0 {
        lemma_pow2_two_e((e - 1) as nat);
        lemma_pow2_2e(e);
    }
}

proof fn lemma_pow2_increase(e: nat)
    requires
        e > 0,
    ensures
        pow2(e) > pow2((e - 1) as nat),
    decreases e,
{
    if e == 1 {
    } else {
        lemma_pow2_increase((e - 1) as nat);
    }
}

#[verifier::nonlinear]
proof fn lemma_mul_upper_bound(x: nat, y: nat, z: nat)
    requires
        x < y,
    ensures
        z * x <= z * y,
{
}

proof fn left_shift_is_pow2(bv: u32, e: u32)
    requires
        e <= 32,
        (bv as nat) * pow2(e as nat) < (0x1_0000_0000 as nat),
    ensures
        (bv << e) as nat == (bv as nat) * pow2(e as nat),
    decreases e,
{
    if e == 0 {
        // assert(bv << 0 == bv * 1u32) by(bit_vector);
        // REVIEW:           ^^^^^^^^^
        //        error: cannot use bit-vector arithmetic on type Int(Int)
        assume(bv << 0 == bv * 1);
        assert((bv << 0) as nat == (bv as nat) * pow2(0)) by (nonlinear_arith)
            requires
                pow2(0) == 1,
                bv << 0 == bv * 1,
        {}
    } else {
        lemma_pow2_increase(e as nat);
        // assert(pow2((e-1) as nat) < pow2(e as nat));
        lemma_mul_upper_bound(pow2((e - 1) as nat), pow2(e as nat), bv as nat);
        // assert((bv as nat) * pow2( (e-1) as nat) <= (bv as nat) * pow2(e as nat));
        // assert((bv as nat) * pow2( (e-1) as nat) < (0x1_0000_0000 as nat));
        left_shift_is_pow2(bv, (e - 1) as u32);
        // assert( (bv << (e-1) as u32) as nat == (bv as nat) * pow2((e-1) as nat));        // we get this from above recursive call
        // assert(bv == bv as nat);
        assert((bv as nat) * pow2((e - 1) as nat) == bv * pow2((e - 1) as nat)) by (nonlinear_arith)
            requires
                (bv == bv as nat),
        {}// assert((bv << (e-1) as u32) as nat == bv* pow2((e-1) as nat));
        // need the above nonlinear fact to make this pass

        assert(pow2(e as nat) == 2 * pow2((e - 1) as nat)) by {
            reveal_with_fuel(pow2, 1);
        }
        assert((bv as nat) * pow2(e as nat) == (bv as nat) * 2 * pow2((e - 1) as nat))
            by (nonlinear_arith)
            requires
                e > 0,
                pow2(e as nat) == 2 * pow2((e - 1) as nat),
                (bv << ((e - 1) as u32)) as nat == bv * pow2((e - 1) as nat),
                (bv as nat) * pow2(e as nat) < (0x1_0000_0000 as nat),
        {}
        assert((2 * (bv << ((e - 1) as u32))) as nat == 2 * ((bv << ((e - 1) as u32)) as nat))
            by (nonlinear_arith)
            requires
                e > 0,
        {}
        left_shift_by_one(bv, e);
        // assert( (bv << e) == (bv << ((e-1) as u32)) << 1);
        left_shift_by_one_is_mul2(bv, e);
        // cannot get the `ensures` clause from this lemma directly
        // since the `ensures` includes `uclip 32` the the RHS, when normal assertions doesn't
        assert(bv << ((e - 1) as u32) < 0x8000_0000) by (nonlinear_arith)
            requires
                (bv << ((e - 1) as u32)) as nat == bv * pow2((e - 1) as nat),
                (bv as nat) * pow2(e as nat) < (0x1_0000_0000 as nat),
                pow2(e as nat) == 2 * pow2((e - 1) as nat),
        {
            // assert( (bv as nat) * pow2((e-1) as nat) * 2 == (bv as nat) * pow2(e as nat));
            // assert( (bv as nat) * pow2((e-1) as nat) < 0x8000_0000);
            // assert(bv * pow2((e-1) as nat) < 0x8000_0000);
        }
        assert(2 * (bv << ((e - 1) as u32)) < 0x1_0000_0000) by (nonlinear_arith)
            requires
                bv << ((e - 1) as u32) < 0x8000_0000,
        {}
        // assert( (bv << e)  == 2 * (bv << ((e-1) as u32)));

        assert((bv << e) as nat == (bv as nat) * pow2(e as nat)) by (nonlinear_arith)
            requires
                e > 0,
                (bv << ((e - 1) as u32)) as nat == bv * pow2((e - 1) as nat),
                (bv << e) as nat == 2 * (bv << ((e - 1) as u32)) as nat,
                pow2(e as nat) == 2 * pow2((e - 1) as nat),
        {
            assert((bv << e) as nat == 2 * ((bv << ((e - 1) as u32)) as nat));
            assert(2 * ((bv << ((e - 1) as u32)) as nat) == (bv as nat) * 2 * pow2((e - 1) as nat));
            assert((bv as nat) * 2 * pow2((e - 1) as nat) == (bv as nat) * pow2(e as nat));
        }
        // assert((bv << e) as nat == (bv as nat) * pow2(e as nat));

    }
}

} // verus!
fn main() {}
