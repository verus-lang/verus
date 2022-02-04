#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[spec]
        fn f() -> int { 1 }

        const C: u64 = 3 + 5;

        #[spec]
        const S: int = C as int + f();

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 code! {
        #[spec]
        fn f() -> int { 1 }

        const C: u64 = 3 + 5;

        #[spec]
        const S: int = C as int + f();

        fn test1() {
            let x = C;
            assert(x == 8);
            assert(S == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 code! {
        const C: u64 = S;
        const S: u64 = C;
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test1_fails3 code! {
        #[spec]
        const C: u64 = S;
        #[spec]
        const S: u64 = C;
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test1_fails4 code! {
        #[spec]
        const C: u64 = 3 + 5;

        const S: int = C as int + 1;
    } => Err(TestErr { has_vir_error: true, .. })
}

test_verify_one_file! {
    #[test] test1_fails5 code! {
        fn f() -> u64 { 1 }

        const S: u64 = 1 + f();
    } => Err(TestErr { has_vir_error: true, .. })
}
