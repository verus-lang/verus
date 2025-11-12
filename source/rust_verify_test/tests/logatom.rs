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
            open_atomic_update!(au, x => {
                assert(x == 2);
                let y = x + 3;
                assert(y == 5);
                y
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] open_atomic_update_proof_simple_err
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
        proof fn function(tracked au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, n => {
                assert(n == 2);
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

test_verify_one_file! {
    #[test] open_atomic_update_spec_fail
    CUSTOM_PREDICATE.to_owned() + verus_code_str! {
        spec fn function(au: AtomicUpdate<i32, i32, MyPredicate>) {
            open_atomic_update!(au, x => {
                assert(x == 2);
                let tracked y = x + 3;
                assert(y == 5);
                y
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot open atomic update in spec mode")
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
            assert (au.outer_mask().is_empty()) by {}
            assert (au.inner_mask().is_empty()) by {}
        }
    } => Ok(())
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
        // make sure `au` knows about `a`
        assert(au.pred().args(a));

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
            let ghost n: u32 = vstd::atomic::pred_args(au.pred());
            assert(au.pred().args(n));
            assert forall |a: u32| au.req(a) <==> a == n by {}
            assert forall |a: u32, b: u32| au.ens(a, b) <==> b == a + 3 by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_missing_update
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        exec fn function() {
            atomic_function(2) atomically |update| {};
        }
    } => Err(err) => assert_vir_error_msg(err, "function must be called in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_too_many_updates
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
    #[test] atomic_call_bad_update_use
    ATOMIC_FUNCTION_ARGS.to_owned() + verus_code_str! {
        exec fn function() {
            let tracked mut num = 2;
            atomic_function(2) atomically |update| {
                assert(num == 2);

                let f = update;
                num = f(num);

                assert(num == 5);
            };
            assert(num == 5);
        }
    } => Err(err) => assert_vir_error_msg(err, "update function must be called directly")
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

test_verify_one_file! {
    #[test] atomic_spec_call_with_self
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub struct Foo {
            pub value: u8,
        }

        impl Foo {
            pub exec fn atomic_function(&self, a: u8)
                atomically (au) {
                    type FunctionPred,
                    (x: u8) -> (y: u8),
                    requires x == self.value + a,
                    ensures y == x + 2,
                },
                requires
                    self.value == 2,
                    a == 3,
            {
                open_atomic_update!(au, mut n => {
                    assert(n == 5);
                    proof { n += 2_u8; };
                    assert(n == 7);
                    n
                });
            }
        }

        pub exec fn other_atomic_function()
            atomically (atom_upd) {
                (a: u8) -> (b: u8),
                requires a == 5,
                ensures b == 7,
            },
        {
            let foo = Foo { value: 2 };

            foo.atomic_function(3) atomically |upd| {
                open_atomic_update!(atom_upd, fst => {
                    assert(fst == 5);
                    let snd = upd(fst);
                    assert(snd == 7);
                    snd
                });
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_spec_mask_simple_ok
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub exec fn atomic_function()
            atomically (au) {
                type FunctionPred,
                (x: u32) -> (y: u32),
                requires x == 2,
                ensures y == 5,
                outer_mask [1_int, 2_int, 3_int],
                inner_mask [1_int, 2_int],
            },
        {
            open_atomic_update!(au, mut n => {
                assert(n == 2);
                proof { n += 3_u32; };
                assert(n == 5);
                n
            });
        }

        proof fn function(tracked au: AtomicUpdate<u32, u32, FunctionPred>) {
            assert forall |a: u32| au.req(a) <==> a == 2 by {}
            assert forall |a: u32, b: u32| au.ens(a, b) <==> b == 5 by {}
            assert (au.outer_mask() == set![1_int, 2_int, 3_int]) by {}
            assert (au.inner_mask() == set![1_int, 2_int]) by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_spec_invalid_mask_pair
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub exec fn atomic_function()
            atomically (au) {
                type FunctionPred,
                (x: u32) -> (y: u32),
                requires x == 2,
                ensures y == 5,
                outer_mask [1_int, 2_int],
                inner_mask [1_int, 2_int, 3_int],
            },
        {
            open_atomic_update!(au, mut n => {
                assert(n == 2);
                proof { n += 3_u32; };
                assert(n == 5);
                n
            });
        }

        pub exec fn caller()
            opens_invariants any
        {
            let tracked mut val = 2;
            atomic_function() atomically |upd| {
                val = upd(val);
            }
        }
    } => Err(err) => {
        // todo: this should emit a note from the recommends check
        // that the mask pair is inverted

        dbg!(&err);

        assert!(!err.errors.is_empty());
        assert!(!err.notes.is_empty());
    }
}

test_verify_one_file! {
    #[test] atomic_spec_not_resolved
    verus_code! {
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
        {}
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic update resolves at end of function")
}

test_verify_one_file! {
    #[test] atomic_spec_not_resolved_cheat
    verus_code! {
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
            assume(au.resolves());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore = "&mut not support"]
    #[test] atomic_spec_mut_ref
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub exec fn atomic_function()
            atomically (au) {
                type FunctionPred,
                (num: &mut u32) -> (_silly: ()),
                requires *old(num) == 2,
                ensures *num == 3,
            },
        {
            open_atomic_update!(au, r => {
                proof { *r += 1_u32; }
            })
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_spec_private_ensures_callee
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub exec fn atomic_function() -> (out: u32)
            atomically (au) {
                type FunctionPred,
                (x: u32) -> (y: u32),
                requires x == 2,
                ensures y == 3,
            },
            ensures
                out == x + y,
        {
            open_atomic_update!(au, value => {
                value + 1_u32
            });

            assert(au.input() == 2);
            assert(au.output() == 3);

            return 5;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_spec_private_ensures_caller
    verus_code! {
        use vstd::*;
        use vstd::prelude::*;
        use vstd::atomic::*;

        pub exec fn atomic_function() -> (out: u32)
            atomically (au) {
                type FunctionPred,
                (x: u32) -> (y: u32),
                requires true,
                ensures x < y,
            },
            ensures
                out == y,
        {
            assume(false);
            unreached()
        }

        pub exec fn other_function() {
            let tracked mut value: u32 = 5;

            let out = atomic_function() atomically |update| {
                value = update(value);
            };

            assert(out > 5);
        }
    } => Ok(())
}
