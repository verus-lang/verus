// Some testcases are ported from https://github.com/secure-foundations/libraries/tree/master/src/NonlinearArithmetic

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// TODO: add testcases for assert_by_nonlinear
// TODO: make sure testcases do not timeout
test_verify_one_file! {
    #[test] test1 code! {
        #[verifier(non_linear)]
        #[proof]
        fn LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int) {
            requires([
                x <= XBound,
                y <= YBound,
                0 <= x,
                0 <= y,
            ]);
            ensures (x * y <= XBound * YBound);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 code! {
        #[verifier(non_linear)]
        #[proof]
        fn LemmaMulStayPositive(x: int, y: int) {
            requires([
                0 <= x,
                0 <= y,
            ]);
            ensures (0 <= x * y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 code! {
        #[verifier(non_linear)]
        #[proof]
        fn LemmaInequalityAfterMul(x: int, y: int, z: int) {
            requires([
                x <= y,
                0 <= z,
            ]);
            ensures (x*z <= y*z);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4 code! {
        #[verifier(non_linear)]
        #[proof]
        fn LemmaDivPosIsPos(x: int, d: int) {
            requires([
                0 <= x,
                0 < d,
            ]);
            ensures(0 <= x / d);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails code! {
        #[verifier(non_linear)]
        #[proof]
        fn wrong_lemma_1(x: int, y: int, z: int) {
            requires([
                x <= y,
                0 <= z,
            ]);
            ensures (x*z < y*z); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test2_fails code! {
        #[verifier(non_linear)]
        #[proof]
        fn wrong_lemma_2(x: int, y: int, z: int) {
            requires([
                x > y,
                3 <= z,
            ]);
            ensures (y*z > x); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
