#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_resolve_1 verus_code! {
        fn user_function() {
            let mut b: u64 = 3;
            let mut c: u64 = 3;
            let m = (&mut b, &mut c);
            let (m1, m2) = m;
            let m3 = callee(m1);
            *m3 = 3;
            if *m3 == 2 {
                resolve(m3);
            }
            *m1 = 3; *m2 = 3;
            resolve(m1); resolve(m2);
            *(&mut b) = 4;
        }

        #[verifier::external_body]
        fn callee(a: &mut u64) -> &mut u64 {
            a
        }
    } => Err(err) => assert_vir_error_msg(err, "a mutable borrow that lives more than a single statement was not explicitly resolved")
}

test_verify_one_file! {
    #[test] test_resolve_2 verus_code! {
        fn user_function() {
            let mut b: u64 = 3;
            let mut c: u64 = 3;
            let m = (&mut b, &mut c);
            let (m1, m2) = m;
            let m3 = callee(m1);
            *m3 = 3;
            if *m3 == 2 {
                resolve(m3);
            }
            *m1 = 3; *m2 = 3;
            resolve(m1); resolve(m2);
            *(&mut b) = 4;
        }

        #[verifier::external_body]
        fn callee(a: &mut u64) -> &mut u64 {
            a
        }
    } => Err(err) => assert_vir_error_msg(err, "a mutable borrow that lives more than a single statement was not explicitly resolved")
}
