#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn f() -> int { 1 }
        const C: u64 = 3 + 5;
        spec const S: int = C as int + f();
        fn e() -> (u: u64) ensures u == 1 { 1 }
        exec const E: u64 ensures E == 2 { 1 + e() }

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 9);
            let y = E;
            assert(y == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        spec fn f() -> int { 1 }
        const C: u64 = 3 + 5;
        spec const S: int = C + f();

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        const C: u64 = S;
        const S: u64 = C;
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test1_fails3 verus_code! {
        spec const C: u64 = S;
        spec const S: u64 = C;
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test1_fails4 verus_code! {
        spec const C: u64 = add(3, 5);
        const S: int = C + 1;
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test1_fails5 verus_code! {
        fn f() -> u64 { 1 }
        const S: u64 = 1 + f();
    } => Err(err) => assert_vir_error_msg(err, "cannot call function with mode exec")
}

test_verify_one_file! {
    #[test] test1_fails6 verus_code! {
        fn e() -> (u: u64) ensures u >= 1 { 1 }
        exec const E: u64 = 1 + e(); // FAILS
    } => Err(e) => assert_vir_error_msg(e, "possible arithmetic underflow/overflow")
}

test_verify_one_file! {
    #[test] test_used_as_spec verus_code! {
        spec const SPEC_E: u64 = 7;
        #[verifier::when_used_as_spec(SPEC_E)]
        exec const E: u64 ensures E == SPEC_E { 7 }

        fn test1() {
            let y = E;
            assert(y == E);
        }
    } => Ok(())
}
