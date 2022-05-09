#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_box_unbox_struct code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        #[proof]
        #[verifier(spinoff_z3)]
        fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a: int = t2.a;
        }

        fn two(v: Thing<u8>) {
            assert(v.a >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_many_queries code! {
        #[proof]
        #[verifier(spinoff_z3)]
        fn test6(x: u32, y: u32, z:u32) {
            requires(x < 0xfff);

            assert_nonlinear_by({
                requires(x < 0xfff);
                ensures(x*x + x == x * (x + 1));
            });
            assert(x*x + x == x * (x + 1));

            assert_bit_vector((x < 0xfff) >>= (x&y < 0xfff));
            assert(x&y < 0xfff);

            assert_nonlinear_by({
                ensures(x*y*z == y*x*z);
            });
        }
    } => Ok(())
}
