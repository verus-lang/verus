#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_assertby1 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert(f1(3) > 3) by {
                reveal(f1);
            }
            assert(f1(3) > 3);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_assertby1_fail1 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert(f1(3) > 4) by { // FAILS
                reveal(f1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_assertby1_fail2 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn assertby_test() {
            assert(f1(3) > 3) by {
                reveal(f1);
            }
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
    #[test] test_forallstmt1_fail1 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: int| f1(x) < x by { // FAILS
                reveal(f1);
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt1_fail2 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: int| f1(x) > x by {
                reveal(f1);
            }
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
    #[test] test_forallstmt2 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: int| 0 <= x implies 1 <= f1(x) by {
                reveal(f1);
            }
            assert(f1(3) > 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt2_fails1 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: int| 0 <= x implies 1 <= f1(x) by {
                reveal(f1);
            }
            assert(f1(-3) > 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_forallstmt2_fails2 verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: int| 1 <= f1(x) by { // FAILS
                reveal(f1);
            }
            assert(f1(3) > 0);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_scope verus_code! {
        spec fn f(j: int) -> bool { true }

        fn scope(b: bool, i: u64) {
            if b {
                let i = 5;
                assert forall|i: int| f(i) by {}
                assert forall|j: int| f(j) by {}
            } else {
                let i = 6;
                assert forall|i: int| f(i) by {}
                assert forall|j: int| f(j) by {}
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt_typ verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: nat| 1 <= f1(x) by {
                reveal(f1);
            }
            assert(f1(3) > 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_forallstmt_typ_fails verus_code! {
        #[verifier(opaque)]
        spec fn f1(i: int) -> int {
            i + 1
        }

        fn forallstmt_test() {
            assert forall|x: nat| 1 <= f1(x) by {} // FAILS
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
