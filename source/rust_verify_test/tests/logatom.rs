#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const CUSTOM_PREDICATE: &'static str = verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                n + 3
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_simple_err
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                n + 7
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic postcondition hold at end of block")
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_immutable_binding
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
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

const ATOMIC_FUNCTION: &'static str = verus_code_str! {
    use vstd::*;
    use vstd::prelude::*;
    use vstd::atomic::*;

    #[verifier::external_body]
    pub exec fn atomic_function()
        atomically (au) {
            type FunctionPred,
            (y: u32) -> (z: u32),
            requires y == 2,
            ensures z == y + 3,
        }
    {}
};

test_verify_one_file! {
    #[test] atomic_spec_predicate_type
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<u32, u32, FunctionPred>) {
            assert forall |a: u32| au.req(a) <==> a == 2 by {}
            assert forall |a: u32, b: u32| au.ens(a, b) <==> b == a + 3 by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_no_update
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function() atomically |update| {};
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_multiple_updates
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function() atomically |update| {
                update(3);
                update(4);
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called exactly once in `atomically` block")
}
