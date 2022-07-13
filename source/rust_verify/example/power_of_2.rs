// Some of the lemmas are ported from the following:
// https://github.com/dafny-lang/libraries/blob/master/src/NonlinearArithmetic/Power2.dfy
// https://github.com/dafny-lang/libraries/blob/master/src/NonlinearArithmetic/Power.dfy

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use builtin_macros::*;


#[spec]
fn pow2(e: nat) -> nat {
    decreases(e);
    if e == 0 { 1 } else { 2 * pow2(e - 1)}
}

#[proof]
fn lemma_pow2_0() {
    ensures(pow2(0) == 1);
}

#[proof]
fn lemma_pow2_unfold3(e: nat) {
    requires(e > 3);
    ensures(pow2(e) == pow2(e-3) * 8);
    reveal_with_fuel(pow2, 3);
}

// (2^e - 1) / 2 = 2^(e - 1) - 1 
#[proof]
fn lemma_pow2_make_div(e: nat) {
    decreases(e);
    requires(e > 0);
    ensures((pow2(e) - 1) / 2 == pow2(e - 1) - 1);

    if e ==1 {}
    else {lemma_pow2_make_div(e-1)}
}

#[proof]
fn lemma_pow2_2e(e: nat) {
    decreases(e);
    requires(e > 0);
    ensures( (pow2(2*e)) == 4 * pow2(2*(e - 1)) );

    reveal_with_fuel(pow2, 2);
    if e ==1 { 
        assert(pow2(2) == 4);
    }
    else {lemma_pow2_2e(e-1)}
}

#[proof]
#[verifier(nonlinear)]
fn lemma_pow2_two_e(e: nat) {
    decreases(e);
    requires(e > 0);
    ensures(pow2(e) * pow2(e) == pow2(2*e));
    
    if e == 1 {}
    else {
        lemma_pow2_two_e(e-1);
        lemma_pow2_2e(e);
    }
}

#[proof]
fn lemma_pow2_increase(e: nat) {
    decreases(e);
    requires(e > 0);
    ensures(pow2(e) > pow2(e-1));
    
    if e == 1 {}
    else {
        lemma_pow2_increase(e-1);
    }
}

#[proof]
#[verifier(bit_vector)]
fn left_shift_by_one(bv:u32, e:u32) {
    decreases(e);
    requires([
        e > 0,
        e <= 32,
    ]);
    ensures( bv << e == (bv << (e-1)) << 1);
}


#[proof]
#[verifier(nonlinear)]
#[verifier(spinoff_prover)]
fn lemma_mul_upper_bound(x: nat, y: nat, z: nat) {
    requires([
        x < y,
    ]);
    ensures (z * x <= z * y);
}

#[proof]
#[verifier(bit_vector)]
fn left_shift_by_one_is_mul2(bv:u32, e:u32) {
    requires([
        e > 0,
        e <= 32,
        bv << e == (bv << (e-1)) << 1,
    ]);
    ensures( (bv << e)  == 2 * (bv << (e-1)));
}

#[proof]
fn left_shift_is_pow2(bv:u32, e:u32) {
    decreases(e);
    requires([
        e <= 32,
        (bv as nat) * pow2(e as nat) < (0x1_0000_0000 as nat),
    ]);
    ensures( (bv << e) as nat == (bv as nat) * pow2(e as nat));

    if e == 0 { 
        assert_bit_vector(bv << 0 == bv * 1);
        assert_nonlinear_by({
            requires([
                pow2(0) == 1,
                bv << 0 == bv * 1,
            ]);
            ensures((bv << 0) as nat == (bv as nat) * pow2(0));
        });
    }
    else {
        lemma_pow2_increase(e);
        assert(pow2((e-1) as nat) < pow2(e as nat));
        lemma_mul_upper_bound( pow2((e-1) as nat), pow2(e as nat), bv as nat);
        assert((bv as nat) * pow2( (e-1) as nat) <= (bv as nat) * pow2(e as nat));
        assert((bv as nat) * pow2( (e-1) as nat) < (0x1_0000_0000 as nat));
        left_shift_is_pow2(bv, e-1);
        assert( (bv << (e-1)) as nat == bv * pow2((e-1) as nat) );  

        assert_by( pow2(e as nat) ==   2 * pow2((e-1) as nat),{
            reveal_with_fuel(pow2, 1);
        });

        assert_nonlinear_by({
            requires([
                e > 0,
                pow2(e as nat) ==   2 * pow2((e-1) as nat),
                (bv << (e-1)) as nat == bv * pow2((e-1) as nat),
                (bv as nat) * pow2(e as nat) < (0x1_0000_0000 as nat),
            ]);
            ensures([
                (bv as nat) * pow2(e as nat) == (bv as nat) * 2 * pow2((e-1) as nat),
                (2 * (bv << (e-1))) as nat == 2 * ((bv << (e-1)) as nat),
            ]);
        }); 
        
        left_shift_by_one(bv, e);
        assert( (bv << e) == (bv << (e-1)) << 1);
        left_shift_by_one_is_mul2(bv, e);
        assert( (bv << e) as nat == 2 * (bv << (e-1)) as nat);

        assert_nonlinear_by({
            requires([
                e > 0,
                (bv << (e-1)) as nat == bv * pow2((e-1) as nat),
                (bv << e) as nat == 2 * (bv << (e-1)) as nat,
                pow2(e as nat) ==   2 * pow2((e-1) as nat),
            ]);
            ensures((bv << e) as nat == (bv as nat) * pow2(e as nat));

            assert((bv << e) as nat == 2 * ((bv << (e-1)) as nat));
            assert( 2 * ((bv << (e-1)) as nat) == (bv as nat) *  2 * pow2((e-1) as nat) );
            assert( (bv as nat) * 2 * pow2((e-1) as nat) == (bv as nat) * pow2(e as nat));
        });

        assert((bv << e) as nat == (bv as nat) * pow2(e as nat));
    }
}

fn main() {}