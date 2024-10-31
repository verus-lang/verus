#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_1 verus_code! {
        struct X {
            i: u8,
            j: u8,
        }

        struct Y {
            x: X,
        }

        fn get_i() -> (res: u8) ensures res == 10 { 10 }

        fn tup_test1() {
            let mut y = (Y { x: X { i: 12, j: 25 } }, 13);
            y.0.x.i = 10;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_2 verus_code! {
        struct S<A> {
            a: A,
            b: i32,
        }

        fn test() {
            let mut s: S<usize> = S { a: 10, b: -10 };
            //s.a = s.a + 1;
            s.a = 3;
        }
    } => Ok(())
}

// identical to poly_has_type_regression_577
test_verify_one_file! {
    #[test] test_3 verus_code! {
        #[verifier::ext_equal]
        struct S {
            n: nat,
            i: int,
        }

        trait T {
            proof fn f(x: &mut S);
        }

        impl T for S {
            proof fn f(x: &mut S) {
                x.n = 3; // breaks has_type unless we add Box(Unbox(x)) == x
                assert(*x =~= S { n: x.n, i: x.i });
            }
        }
    } => Ok(())
}
