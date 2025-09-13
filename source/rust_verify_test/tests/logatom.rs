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
                n += 3_i32;
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
                n += 3_i32;
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

    pub exec fn atomic_function()
        atomically (au) {
            type FunctionPred,
            (x: u32) -> (y: u32),
            requires x == 2,
            ensures y == 5,
        },
    {
        open_atomic_update!(au, mut n => {
            assert(n == 2);
            proof { n += 3_u32; };
            assert(n == 5);
            n
        });
    }
};

test_verify_one_file! {
    #[test] atomic_spec_predicate_type
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<u32, u32, FunctionPred>) {
            assert forall |a: u32| au.req(a) <==> a == 2 by {}
            assert forall |a: u32, b: u32| au.ens(a, b) <==> b == 5 by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_missing_update
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function() atomically |update| {};
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_too_many_updates
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function() atomically |update| {
                update(3);
                update(4);
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called exactly once in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_simple
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        exec fn function() {
            let tracked mut num = 2;
            atomic_function() atomically |update| {
                assert(num == 2);
                num = update(num);
                assert(num == 5);
            };
            assert(num == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_from_atomic_function
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        pub exec fn other_atomic_function()
            atomically (atom_upd) {
                (a: u32) -> (b: u32),
                requires a == 2,
                ensures b == 5,
            },
        {
            atomic_function() atomically |upd| {
                open_atomic_update!(atom_upd, fst => {
                    assert(fst == 2);
                    let snd = upd(fst);
                    assert(snd == 5);
                    snd
                });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_fail_atomic_pre
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        pub exec fn other_atomic_function()
            atomically (atom_upd) {
                (a: u32) -> (b: u32),
                requires a == 3,
                ensures b == 5,
            },
        {
            atomic_function() atomically |upd| {
                open_atomic_update!(atom_upd, mut num => {
                    num = upd(num);
                    num
                });
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic precondition holds before update function")
}

const ATOMIC_FUNCTION_ARGS: &'static str = verus_code_str! {
    use vstd::*;
    use vstd::prelude::*;
    use vstd::atomic::*;

    pub exec fn atomic_function(a: u32)
        atomically (au) {
            type FunctionPred,
            (x: u32) -> (y: u32),
            requires x == a,
            ensures y == x + 3,
        },
        requires a == 2,
    {
        open_atomic_update!(au, mut n => {
            assert(n == 2);
            proof { n += 3_u32; };
            assert(n == 5);
            n
        });
    }
};

test_verify_one_file! {
    #[test] atomic_spec_predicate_type_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<u32, u32, FunctionPred>) {
            let ghost FunctionPred { data: (n) } = au.pred();
            assert forall |a: u32| au.req(a) <==> a == n by {}
            assert forall |a: u32, b: u32| au.ens(a, b) <==> b == a + 3 by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_missing_update_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function(2) atomically |update| {};
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_too_many_updates_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function(2) atomically |update| {
                update(3);
                update(4);
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called exactly once in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_simple_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        exec fn function() {
            let tracked mut num = 2;
            atomic_function(2) atomically |update| {
                assert(num == 2);
                num = update(num);
                assert(num == 5);
            };
            assert(num == 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_from_atomic_function_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        pub exec fn other_atomic_function()
            atomically (atom_upd) {
                (a: u32) -> (b: u32),
                requires a == 2,
                ensures b == 5,
            },
        {
            atomic_function(2) atomically |upd| {
                open_atomic_update!(atom_upd, fst => {
                    assert(fst == 2);
                    let snd = upd(fst);
                    assert(snd == 5);
                    snd
                });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_fail_atomic_pre_args
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        pub exec fn other_atomic_function()
            atomically (atom_upd) {
                (a: u32) -> (b: u32),
                requires a == 3,
                ensures b == 6,
            },
        {
            atomic_function(2) atomically |upd| {
                open_atomic_update!(atom_upd, mut num => {
                    num = upd(num);
                    num
                });
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic precondition holds before update function")
}
