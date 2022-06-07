// most of the codes are copied from: https://github.com/utaal/verified-nrkernel/blob/main/page-table/lib.rs

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use builtin_macros::*;


#[proof] #[verifier(integer_ring)]
pub fn mod_of_mul_int(a: int, b: int) {
    ensures((a * b) % b == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn mod_of_mul(a: nat, b: nat) {
    requires(b > 0);
    ensures((a * b) % b == 0);

    mod_of_mul_int(a,b);
    // if a == 0 {}
    // else {
    //     assert(a > 0);
    //     assert(b > 0);
    //     assert(a*b > 0);
    //     assert( (a*b) % b >= 0);
    // }
}


#[proof] #[verifier(integer_ring)]
pub fn mod_add_zero_int(a: int, b: int, c: int) {
    requires([
        a % c == 0,
        b % c == 0,
    ]);
    ensures((a + b) % c == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn mod_add_zero(a: nat, b: nat, c: nat) {
    requires([
        a % c == 0,
        b % c == 0,
        c > 0,
    ]);
    ensures((a + b) % c == 0);
    mod_add_zero_int(a,b,c);
}


#[proof] #[verifier(integer_ring)]
pub fn subtract_mod_aligned_int(a: int, b: int) {
    ensures((a - (a % b)) % b == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn subtract_mod_aligned(a: nat, b: nat) {
    requires(0 < b);
    ensures((a - (a % b)) % b == 0);

    subtract_mod_aligned_int(a,b);
}


#[proof] #[verifier(integer_ring)]
pub fn mod_mult_zero_implies_mod_zero_int(a: int, b: int, c: int) {
    requires(a % (b * c) == 0);
    ensures(a % b == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) {
    requires([
        a % (b * c) == 0,
        b > 0,
        c > 0,
    ]);
    ensures(a % b == 0);
    mod_mult_zero_implies_mod_zero_int(a,b,c);
}


#[proof] #[verifier(integer_ring)]
pub fn subtract_mod_eq_zero_int(a: int, b: int, c: int) {
    requires([
             a % c == 0,
             b % c == 0,
    ]);
    ensures((b - a) % c == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn subtract_mod_eq_zero(a: nat, b: nat, c: nat) {
    requires([
             a % c == 0,
             b % c == 0,
             a <= b,
             c > 0, 
    ]);
    ensures((b - a) % c == 0);
    subtract_mod_eq_zero_int(a,b,c);
}


#[proof] #[verifier(integer_ring)]
pub fn multiple_offsed_mod_gt_0_int(a: int, b: int, c: int, ac:int, bc:int,  abc:int) {
    requires([
        ac == a%c,
        bc == b%c,
        abc == (a-b) % c,
    ]);
    ensures( (ac - bc - abc) % c == 0);
}
#[proof] #[verifier(nonlinear)]
pub fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) {
    requires([
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ]);
    ensures((a - b) % c > 0);
    multiple_offsed_mod_gt_0_int(a,b,c, (a%c) as int, (b%c) as int, ((a-b)%c) as int);
}

fn main() {}