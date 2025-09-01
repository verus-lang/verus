#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const COMMON: &'static str = verus_code_str! {
    use vstd::*;
    use vstd::prelude::*;
    use vstd::atomic::*;

    struct MyPredicate;
    impl UpdatePredicate<i32, i32> for MyPredicate {
        open spec fn req(self, x: i32) -> bool { x == 2 }
        open spec fn ens(self, x: i32, y: i32) -> bool { y == 5 }
    }
};

test_verify_one_file! {
    #[test] open_atomic_update_proof_simple_ok
    COMMON.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                n + 3
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_simple_err
    COMMON.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                n + 7
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic postcondition hold at end of block")
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_immutable_binding
    COMMON.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                n += 3;
                n
            });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign twice to immutable variable `n`")
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_mutable_binding
    COMMON.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, mut n => {
                n += 3;
                n
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_atomic_update_exec_simple_ok
    COMMON.to_owned() + verus_code_str! {
        exec fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, x => {
                assert(x == 2);
                let tracked y = x + 3;
                assert(y == 5);
                y
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_atomic_update_exec_simple_err
    COMMON.to_owned() + verus_code_str! {
        exec fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                assert(n == 2);
                n + 7
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic postcondition hold at end of block")
}

test_verify_one_file! {
    #[test] open_atomic_update_exec_immutable_binding
    COMMON.to_owned() + verus_code_str! {
        exec fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                assert(n == 2);
                proof { n += 3_i32; }
                assert(n == 5);
                n
            });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign twice to immutable variable `n`")
}

test_verify_one_file! {
    #[test] open_atomic_update_exec_mutable_binding
    COMMON.to_owned() + verus_code_str! {
        exec fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, mut n => {
                assert(n == 2);
                proof { n += 3_i32; }
                assert(n == 5);
                n
            });
        }
    } => Ok(())
}
