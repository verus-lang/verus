#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] real_basics verus_code! {
        proof fn test(i: int, x: real, y: real) {
            assert(x == 0.2real ==> x / 2.0 == 0.1real);
            assert(x > 0.0 ==> x / 3.0 > 0.0);
            assert(x <= 1.0 ==> x / 3.0 < 1.0);
            let z: real = x + 1.1;
            assert(z > x);
            let q: real = 5u8 as real;
            assert(q == 5real);
            assert((i + 1) as real == i as real + 1.0);
            assert(x >= 0.0 ==> x / 3.0 > 0.0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] real_nonlinear1 verus_code! {
        proof fn test_nonlinear(a: real, b: real, q: real) {
            assert(a >= 0.0 && b >= 0.0 && a * a + b * b == (a * b + 1.0) * q ==> q >= 0.0)
                by (nonlinear_arith);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] real_nonlinear2 verus_code! {
        proof fn test_nonlinear(a: real, b: real, q: real) {
            // This is true, but we expect that it requires nonlinear_arith:
            assert(a >= 0.0 && b >= 0.0 && a * a + b * b == (a * b + 1.0) * q ==> q >= 0.0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
