#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_assertby1 code! {
        #[spec]
        #[verifier(opaque)]
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
        #[verifier(opaque)]
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
        #[verifier(opaque)]
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
    #[test] test_assertby1_fail3 code! {
        #[proof]
        fn consume(#[proof] x: bool) {
        }

        fn assertby_proof_var_disallowed(#[proof] x: bool) {
            assert_by(true, consume(x));
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_forallstmt1 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                ensures(f1(x) > x);
                reveal(f1);
            });
            assert(f1(3) > 3);
        }

        fn forallstmt_test_inference() {
            assert_forall_by(|x| {
                ensures(f1(x) > x);
                reveal(f1);
            });
            assert(f1(3) > 3);
        }

        #[proof]
        fn no_consume(x: bool) {
        }

        fn forallstmt_proof_var_allowed_as_spec(#[proof] x: bool) {
            assert_forall_by(|i: int| {
                ensures(f1(i) == f1(i));
                no_consume(x);
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail1 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                ensures(f1(x) < x); // FAILS
                reveal(f1);
            });
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail2 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                ensures(f1(x) > x);
                reveal(f1);
            });
            assert(f1(3) == 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail3 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        #[proof]
        fn consume(#[proof] x: bool) {
        }

        fn forallstmt_proof_var_disallowed(#[proof] x: bool) {
            assert_forall_by(|i: int| {
                ensures(f1(i) == f1(i));
                consume(x);
            });
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test_forallstmt2 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                requires(0 <= x);
                ensures(1 <= f1(x));
                reveal(f1);
            });
            assert(f1(3) > 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt2_fails1 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                requires(0 <= x);
                ensures(1 <= f1(x));
                reveal(f1);
            });
            assert(f1(-3) > 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt2_fails2 code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: int| {
                ensures(1 <= f1(x)); // FAILS
                reveal(f1);
            });
            assert(f1(3) > 0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_scope code! {
        #[spec]
        fn f(j: int) -> bool { true }

        fn scope(b: bool, i: u64) {
            if b {
                let i = 5;
                assert_forall_by(|i: int| {ensures(f(i));});
                assert_forall_by(|j: int| {ensures(f(j));});
            } else {
                let i = 6;
                assert_forall_by(|i: int| {ensures(f(i));});
                assert_forall_by(|j: int| {ensures(f(j));});
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt_typ code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: nat| {
                ensures(1 <= f1(x));
                reveal(f1);
            });
            assert(f1(3) > 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt_typ_fails code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: nat| {
                ensures(1 <= f1(x)); // FAILS
            });
            assert(f1(3) > 0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assertby1_let code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert_by({ #[spec] let a = 3; f1(a) > a }, reveal(f1));
            assert(f1(3) > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt_let code! {
        #[spec]
        #[verifier(opaque)]
        fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert_forall_by(|x: nat| {
                ensures({ #[spec] let a = 1; a <= #[trigger] f1(x) });
                reveal(f1);
            });
            assert(f1(3) > 0);
        }
    } => Ok(())
}
