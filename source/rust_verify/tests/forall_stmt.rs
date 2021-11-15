#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_assertby1 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert_by(f1(3) > 3, reveal(f1));
            assert(f1(3) > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assertby1_fail1 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert_by(f1(3) > 4, reveal(f1)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assertby1_fail2 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert_by(f1(3) > 3, reveal(f1));
            assert(f1(3) == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt1 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            forall(|x:int| {
                ensures(f1(x) > x);
                reveal(f1);
            });
            assert(f1(3) > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail1 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            forall(|x:int| {
                ensures(f1(x) < x); // FAILS
                reveal(f1);
            });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail2 code! {
        #[spec]
        #[opaque]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            forall(|x:int| {
                ensures(f1(x) > x);
                reveal(f1);
            });
            assert(f1(3) == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
