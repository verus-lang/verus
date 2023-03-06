#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_stmts_expr_1 verus_code! {
        fn id(v: u64) -> (ret: u64)
            ensures v == ret
        {
            v
        }

        fn test1() {
            let mut a = 12;
            let b = id({
                a = a + 1;
                a
            });
            assert(b == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_stmts_expr_2 verus_code! {
        fn id(v: &u64) -> (ret: u64)
            ensures *v == ret
        {
            *v
        }

        fn test1() {
            let mut a = 12;
            let b = id({
                a = a + 1;
                &a
            });
            assert(b == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_stmts_expr_3 verus_code! {
        fn id(v: &mut u64)
            ensures *v == *old(v)
        {
        }

        fn test1() {
            let mut a = 12;
            // this may or may not be supported later, it is intentionally unsupported now
            id({
                a = a + 1;
                &mut a
            });
            assert(a == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_stmts_expr_ref_mut verus_code! {
        #[derive(Debug)]
        struct A {
            v: u64,
        }

        fn ret_ref_mut(a: &mut A) -> &mut u64 {
            &mut a.v
        }

        fn transform(v: &mut u64) {
            *v += 1;
            println!("{}", v);
        }

        fn main() {
            let mut a = A { v: 23 };
            // this may or may not be supported later, it is intentionally unsupported now
            transform({
                let b = &mut a;
                b.v += 2;
                ret_ref_mut(b)
            });
            println!("{:?}", a)
        }
    } => Ok(())
}
