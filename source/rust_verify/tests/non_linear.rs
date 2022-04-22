// Some testcases are ported from https://github.com/secure-foundations/libraries/tree/master/src/NonlinearArithmetic

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// TODO: make sure testcases do not timeout

// Test #[verifier(non_linear)]
test_verify_one_file! {
    #[test] test1 code! {
        #[verifier(non_linear)]
        #[proof]
        fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int) {
            requires([
                x <= x_bound,
                y <= y_bound,
                0 <= x,
                0 <= y,
            ]);
            ensures (x * y <= x_bound * y_bound);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 code! {
        #[verifier(non_linear)]
        #[proof]
        fn lemma_mul_stay_positive(x: int, y: int) {
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
        fn lemma_inequality_after_mul(x: int, y: int, z: int) {
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
        fn lemma_div_pos_is_pos(x: int, d: int) {
            requires([
                0 <= x,
                0 < d,
            ]);
            ensures(0 <= x / d);
        }
    } => Ok(())
}

// Test assert_by_nonlinear
test_verify_one_file! {
    #[test] test5 code! {
        #[proof]
        fn test5_bound_checking(x: u32, y: u32, z:u32) {
            requires([
                x <= 0xffff,
                y <= 0xffff,
                z <= 0xffff,
            ]);

            assert_by_nonlinear( (x as int) * (z as int) == ((x*z) as int), {
                requires([
                    x <= 0xffff,
                    z <= 0xffff,
                ]);
                assert(0 <= (x as int) * (z as int));
                assert((x as int) * (z as int) <= 0xffff*0xffff);
            });
            assert((x as int) * (z as int) == ((x*z) as int));

            assert_by_nonlinear((y as int) * (z as int) == ( (y*z) as int), {
                requires([
                    y <= 0xffff,
                    z <= 0xffff,
                ]);
                assert(0 <= (y as int) * (z as int));
                assert((y as int) * (z as int) <= 0xffff*0xffff);
            });
            assert((y as int) * (z as int) == ((y*z) as int));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test6 code! {
        #[proof]
        fn test6(x: u32, y: u32, z:u32) {
            requires(x < 0xfff);

            assert_by_nonlinear(x*x + x == x * (x + 1), {
                requires(x < 0xfff);
            });
            assert(x*x + x == x * (x + 1));

            assert_by_nonlinear(x*y == y*x, {});
            assert(x*y == y*x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test7 code! {
        #[proof]
        fn test6(x: int, y: int, z:int) {
            assert_by_nonlinear( (x+y)*z == x*z + y*z, {});
            assert( (x+y)*z == x*z + y*z);

            assert_by_nonlinear( (x-y)*z == x*z - y*z, {});
            assert( (x-y)*z == x*z - y*z);
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

test_verify_one_file! {
    #[test] test3_fails code! {
        #[proof]
        fn test3_fails(x: int, y: int, z: int) {
            assert_by_nonlinear(x*y == y*z,{}) // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test4_fails code! {
        #[proof]
        fn test4_fails(x: u32, y: u32, z: u32) {
            assert_by_nonlinear( (x as int) * (z as int) == ((x*z) as int), {}); //FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
