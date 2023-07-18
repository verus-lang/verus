// most of the codes are copied from: https://github.com/utaal/verified-nrkernel/blob/main/page-table/lib.rs

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use vstd::{*, pervasive::*};
#[allow(unused_imports)]
use builtin_macros::*;


verus!{

proof fn mod_of_mul_int(a: int, b: int) by(integer_ring) {
    ensures((a * b) % b == 0);
}

proof fn mod_of_mul(a: nat, b: nat) by(nonlinear_arith) 
    requires b > 0
    ensures  (a * b) % b == 0
{

    mod_of_mul_int(a as int ,b as int);
    // if a == 0 {}
    // else {
    //     assert(a > 0);
    //     assert(b > 0);
    //     assert(a*b > 0);
    //     assert( (a*b) % b >= 0);
    // }
}


pub proof fn mod_add_zero_int(a: int, b: int, c: int) by(integer_ring) 
    requires
        a % c == 0,
        b % c == 0,
    ensures 
        (a + b) % c == 0
{}

pub proof fn mod_add_zero(a: nat, b: nat, c: nat) by(nonlinear_arith) 
    requires
        a % c == 0,
        b % c == 0,
        c > 0,
    ensures (a + b) % c == 0

{
    mod_add_zero_int(a as int,b as int,c as int);
}


pub proof fn subtract_mod_aligned_int(a: int, b: int) by(integer_ring) 
    ensures (a - (a % b)) % b == 0
{
    
}
pub proof fn subtract_mod_aligned(a: nat, b: nat) by(nonlinear_arith) 
    requires 0 < b
    ensures (a - (a % b)) % (b as int) == 0
{
    subtract_mod_aligned_int(a as int,b as int);
}


pub proof fn mod_mult_zero_implies_mod_zero_int(a: int, b: int, c: int) by(integer_ring)
    requires a % (b * c) == 0
    ensures a % b == 0
{
}

pub proof fn mod_mult_zero_implies_mod_zero(a: nat, b: nat, c: nat) by(nonlinear_arith) 
    requires
        a % (b * c) == 0,
        b > 0,
        c > 0,
    ensures a % b == 0
{
    mod_mult_zero_implies_mod_zero_int(a as int,b as int,c as int);
}


pub proof fn subtract_mod_eq_zero_int(a: int, b: int, c: int) by(integer_ring) 
    requires
             a % c == 0,
             b % c == 0,
    ensures (b - a) % c == 0
{}
pub proof fn subtract_mod_eq_zero(a: nat, b: nat, c: nat) by(nonlinear_arith) 
    requires
             a % c == 0,
             b % c == 0,
             a <= b,
             c > 0, 
    ensures (b - a) % (c as int) == 0
{
    subtract_mod_eq_zero_int(a as int,b as int,c as int);
}


pub proof fn multiple_offsed_mod_gt_0_int(a: int, b: int, c: int, ac:int, bc:int,  abc:int) by(integer_ring)
    requires
        ac == a%c,
        bc == b%c,
        abc == (a-b) % c,
    ensures (ac - bc - abc) % c == 0
{}
pub proof fn multiple_offsed_mod_gt_0(a: nat, b: nat, c: nat) by(nonlinear_arith) 
    requires
        a > b,
        c > 0,
        b % c == 0,
        a % c > 0,
    ensures (a - b) % (c as int) > 0
{
    multiple_offsed_mod_gt_0_int(a as int,b as int,c as int, (a%c) as int, (b%c) as int, ((a-b)%(c as int)) as int);
}

fn main() {}

}