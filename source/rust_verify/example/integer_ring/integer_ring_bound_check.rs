// testcases and examples are ported from below two files 
// 1. https://github.com/secure-foundations/dafny/blob/b402d2aeb6129603277e35fcef33bf1024f4b217/Test/gb_test.dfy
// 2. https://github.com/secure-foundations/veri-titan/blob/master/lib/generic_mm_lemmas.dfy
// 
// With references from:
// https://github.com/secure-foundations/libraries/blob/master/src/NonlinearArithmetic/Mul.dfy

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
mod pervasive;
#[allow(unused_imports)]
use pervasive::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[verifier(integer_ring)]
#[verifier::proof]
fn ModAfterMul(x: int, y: int, z:int, m:int){
    requires( (x-y) % m == 0);
    ensures( (x*z - y*z) % m == 0);
}

// bound check lemmas
#[verifier(nonlinear)]  
#[verifier(external_body)]
#[verifier::proof]
fn LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int) {
    requires([
        x <= XBound,
        y <= YBound,
        0 <= x,
        0 <= y,
    ]);
    ensures (x * y <= XBound * YBound);
}

#[verifier(nonlinear)] 
#[verifier::proof]
fn LemmaMulStayPositive(x: int, y: int) {
    requires([
        0 <= x,
        0 <= y,
    ]);
    ensures (0 <= x * y);
}

#[verifier(nonlinear)] 
#[verifier::proof]
fn LemmaInequalityAfterMul(x: int, y: int, z: int) {
    requires([
        x <= y,
        0 <= z,
    ]);
    ensures (x*z <= y*z);
}

#[verifier::proof]
fn ModAfterMul_u32(x: u32, y:u32 , z:u32, m:u32){
    requires([
        m > 0,
        (x-y) % m == 0,
        x >= y,
        x <= 0xffff,
        y <= 0xffff,
        z <= 0xffff,
        m <= 0xffff,
    ]);
    ensures((x*z - y*z) % m == 0);

    ModAfterMul(x as int,y as int,z as int,m as int);

    // below are for bound checks
    // every single operation is in bound: x*z, y*z, (x*z - y*z)
    LemmaMulUpperBound(x, 0xffff, z, 0xffff);
    LemmaMulStayPositive(x,z);
    // assert( (x as int) * (z as int) == ( (x*z) as int));

    LemmaMulUpperBound(y, 0xffff, z, 0xffff);
    LemmaMulStayPositive(y,z);
    // assert( (y as int) * (z as int) == ( (y*z) as int));

    LemmaInequalityAfterMul(y,x,z);
    // assert( (((x*z - y*z) as int) % (m as int)) ==  (((x*z) as int) - ((y*z) as int)) % (m as int));
}

#[verifier::proof]
fn ModAfterMul_u32_with_assert_by_nonlinear(x: u32, y:u32 , z:u32, m:u32){
    requires([
        m > 0,
        (x-y) % m == 0,
        x >= y,
        x <= 0xffff,
        y <= 0xffff,
        z <= 0xffff,
        m <= 0xffff,
    ]);
    ensures((x*z - y*z) % m == 0);

    ModAfterMul(x as int,y as int,z as int,m as int);
    
    assert_nonlinear_by({
        requires([
            x <= 0xffff,
            z <= 0xffff,
        ]);
        ensures((x as int) * (z as int) == ((x*z) as int));
        assert(0 <= (x as int) * (z as int));
        assert((x as int) * (z as int) <= 0xffff*0xffff);
    });
    assert((x as int) * (z as int) == ((x*z) as int));

    assert_nonlinear_by({
        requires([
            y <= 0xffff,
            z <= 0xffff,
        ]);
        ensures((y as int) * (z as int) == ( (y*z) as int));
        assert(0 <= (y as int) * (z as int));
        assert((y as int) * (z as int) <= 0xffff*0xffff);
    });
    assert((y as int) * (z as int) == ( (y*z) as int));

    // below `assert_nonlinear_by` timeouts now in newer z3
    // assert_nonlinear_by({
    //     requires([
    //         x <= 0xffff,
    //         y <= 0xffff,
    //         z <= 0xffff,
    //         ((x as int) * (z as int) == ( (x*z) as int)),
    //         ((y as int) * (z as int) == ( (y*z) as int)),
    //         (y <= x),
    //         (0 <= z),
    //     ]);
    //     ensures(y*z <= x*z);
    // });
    LemmaInequalityAfterMul(y,x,z);
    assert(y*z <= x*z);
}

fn main() {}