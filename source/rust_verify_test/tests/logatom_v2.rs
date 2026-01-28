#![feature(rustc_private)]
#[macro_use]
mod common;
use std::sync::LazyLock;

use common::*;

const TOKEN_LIB: &'static str = verus_code_str! {
    use vstd::*;
    use vstd::prelude::*;
    use vstd::atomic::*;

    pub struct Token {
        state: u16,
    }

    impl Token {
        pub closed spec fn is_valid(self) -> bool {
            self.state <= 1000
        }

        proof fn with_state(tracked state: u16) -> (tracked out: Self)
            ensures out.state == state,
        {
            Self { state }
        }

        pub proof fn new() -> (tracked out: Self)
            ensures out.is_valid(),
        {
            Self::with_state(250)
        }

        pub proof fn invalid() -> (tracked out: Self)
            ensures !out.is_valid(),
        {
            Self::with_state(2000)
        }

        pub proof fn modify(tracked &mut self)
            requires old(self).is_valid(),
            ensures self.is_valid(),
        {
            self.state = (1000 - self.state) as u16;
        }
    }
};

test_verify_one_file! {
    #[test] token_lib_def TOKEN_LIB.to_owned() => Ok(())
}

test_verify_one_file! {
    #[test] atomic_function_commit_only
    TOKEN_LIB.to_owned() + verus_code_str! {
        pub fn atomic_function()
            atomically (atomic_update) {
                (x: Token) -> (y: Result<Token, Token>),
                requires x.is_valid(),
                ensures match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
            },
        {
            let res = try_open_atomic_update!(atomic_update, token => {
                Tracked(Ok(token))
            });

            assert(res@ is Ok);
            assert(res@->Ok_0 == ());
            assert(atomic_update.resolves());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_function_commit_fail_atomic_post
    TOKEN_LIB.to_owned() + verus_code_str! {
        pub fn atomic_function()
            atomically (atomic_update) {
                (x: Token) -> (y: Result<Token, Token>),
                requires x.is_valid(),
                ensures match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
            },
        {
            try_open_atomic_update!(atomic_update, token => {
                Tracked(Ok(Token::invalid()))
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic postcondition hold at end of block")
}

test_verify_one_file! {
    #[test] atomic_function_abort_only
    TOKEN_LIB.to_owned() + verus_code_str! {
        pub fn atomic_function()
            atomically (atomic_update) {
                (x: Token) -> (y: Result<Token, Token>),
                requires x.is_valid(),
                ensures match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
            },
        {
            let tracked au = atomic_update;
            let res = try_open_atomic_update!(au, token => {
                Tracked(Err(token))
            });

            assert(res@ is Err);
            assert(res@->Err_0 == atomic_update);
            assume(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_function_abort_fail_atomic_post
    TOKEN_LIB.to_owned() + verus_code_str! {
        pub fn atomic_function()
            atomically (atomic_update) {
                (x: Token) -> (y: Result<Token, Token>),
                requires x.is_valid(),
                ensures match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
            },
        {
            try_open_atomic_update!(atomic_update, token => {
                Tracked(Err(Token::invalid()))
            });
        }
    } => Err(err) => assert_any_vir_error_msg(err, "cannot show atomic postcondition hold at end of block")
}

test_verify_one_file! {
    #[test] atomic_function_abort_and_commit
    TOKEN_LIB.to_owned() + verus_code_str! {
        pub fn atomic_function()
            atomically (atomic_update) {
                (x: Token) -> (y: Result<Token, Token>),
                requires x.is_valid(),
                ensures match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
            },
        {
            let tracked au = atomic_update;
            let res = try_open_atomic_update!(au, token => {
                Tracked(Err(token))
            });

            assert(res@ is Err);
            let tracked au = res.get().tracked_unwrap_err();
            assert(au == atomic_update);

            let res = try_open_atomic_update!(au, mut token => {
                proof { token.modify() };
                Tracked(Ok(token))
            });

            assert(res@ is Ok);
            assert(atomic_update.resolves());
        }
    } => Ok(())
}

static ATOMIC_FUNCTION: LazyLock<String> = LazyLock::new(|| {
    TOKEN_LIB.to_owned()
        + verus_code_str! {
            type FunAU = AtomicUpdate<Token, Result<Token, Token>, FunPred>;

            pub fn atomic_function()
                atomically (atomic_update) {
                    type FunPred,
                    (x: Token) -> (y: Result<Token, Token>),
                    requires x.is_valid(),
                    ensures match y {
                        Ok(t) => t.is_valid(),
                        Err(t) => t == x,
                    },
                },
            {
                assume(atomic_update.resolves());
            }

            uninterp spec fn cond<X>(x: X) -> bool;
        }
});

test_verify_one_file! {
    #[test] atomic_function_def ATOMIC_FUNCTION.to_owned() => Ok(())
}

test_verify_one_file! {
    #[test] atomic_function_predicate_type
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        pub proof fn check_predicate_type(
            tracked au: FunAU,
            tracked x: Token,
            tracked y: Result<Token, Token>,
        )
            ensures
                au.req(x) <==> x.is_valid(),
                au.ens(x, y) <==> match y {
                    Ok(t) => t.is_valid(),
                    Err(t) => t == x,
                },
                au.outer_mask().is_empty(),
                au.inner_mask().is_empty(),
        {}
    }
    => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_assume_both
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked res: Result<Token, Token> = update(Token::new());
                if cond(res) {
                    assume(res.branch() == UpdateControlFlow::Commit);
                    break;
                } else {
                    assume(res.branch() == UpdateControlFlow::Abort);
                    continue;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_fail_commit
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked res: Result<Token, Token> = update(Token::new());
                if cond(res) {
                    break;
                } else {
                    assume(res.branch() == UpdateControlFlow::Abort);
                    continue;
                }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "cannot show the atomic update was committed")
}

test_verify_one_file! {
    #[test] atomic_call_fail_abort
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked res: Result<Token, Token> = update(Token::new());
                if cond(res) {
                    assume(res.branch() == UpdateControlFlow::Commit);
                    break;
                } else {
                    continue;
                }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "cannot show the atomic update was aborted")
}

test_verify_one_file! {
    #[test] atomic_call_fail_abort_implicit
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked res: Result<Token, Token> = update(Token::new());
                if cond(res) {
                    assume(res.branch() == UpdateControlFlow::Commit);
                    break;
                }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "cannot show the atomic update was aborted")
}

test_verify_one_file! {
    #[test] atomic_call_no_update
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {}
        }
    } => Err(err) => assert_any_vir_error_msg(err, "function must be called in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_multiple_updates
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked _ = update(Token::new());
                let tracked _ = update(Token::new());
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "function must be called exactly once in `atomically` block")
}

test_verify_one_file! {
    #[test] atomic_call_success
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            let tracked mut token = Token::new();
            atomic_function() atomically |update|
                invariant token.is_valid(),
            {
                let tracked res: Result<Token, Token> = update(token);
                match res {
                    Ok(t) => break,
                    Err(t) => token = t,
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_success_loop_isolation
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(true)]
        fn atomic_function_call() {
            let tracked mut token = Token::new();
            atomic_function() atomically |update| -> (au: FunAU)
                invariant token.is_valid(),
                ensures au.resolves(),
            {
                let tracked res: Result<Token, Token> = update(token);
                match res {
                    Ok(t) => {
                        assert(res.branch() == UpdateControlFlow::Commit);
                        assert(au.resolves());
                        break;
                    }

                    Err(t) => {
                        assert(res.branch() == UpdateControlFlow::Abort);
                        token = t;
                        continue;
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_with_labels
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            let tracked mut token = Token::new();
            atomic_function() 'label: atomically |update| -> (au: FunAU)
                invariant token.is_valid(),
            {
                let tracked res = update(token);
                match res {
                    Ok(t) => break 'label,
                    Err(t) => {
                        token = t;
                        continue 'label;
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_call_fail_atomic_pre
    ATOMIC_FUNCTION.to_owned() + verus_code_str! {
        #[verifier::loop_isolation(false)]
        fn atomic_function_call() {
            atomic_function() atomically |update| {
                let tracked _ = update(Token::invalid());
                assume(false);
                break;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show atomic precondition holds before update function")
}

test_verify_one_file! {
    #[test] atomic_spec_empty
    verus_code! {
        use vstd::atomic::*;
        pub exec fn atomic_function()
            atomically (au) {},
        {
            try_open_atomic_update!(au, _unit => {
                Tracked(())
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] atomic_spec_check_defaults
    verus_code! {
        use vstd::atomic::*;
        pub exec fn atomic_function()
            atomically (au) {
                type PredType,
            },
        {
            try_open_atomic_update!(au, _unit => {
                Tracked(())
            });
        }

        pub proof fn check_predicate_type(
            tracked au: AtomicUpdate<(), (), PredType>,
            tracked x: (),
            tracked y: (),
        )
            ensures
                au.req(x),
                au.ens(x, y),
                au.outer_mask().is_empty(),
                au.inner_mask().is_empty(),
        {}
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
                (x: u32) -> (y: I<u32>),
                requires x == 2,
                ensures y@ == 3,
            },
            ensures out == x + y@,
        {
            try_open_atomic_update!(au, value => {
                Tracked(I((value + 1_u32) as u32))
            });

            assert(au.input() == 2);
            assert(au.output()@ == 3);

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
                (x: u32) -> (y: I<u32>),
                ensures x < y@,
            },
            ensures out == y@,
        {
            assume(false);
            unreached()
        }

        #[verifier::loop_isolation(false)]
        pub exec fn other_function() {
            let tracked mut value: u32 = 5;

            let out = atomic_function() atomically |update|
                invariant value == 5,
            {
                let tracked I(next) = update(value);
                value = next;
                break;
            };

            assert(out > 5);
        }
    } => Ok(())
}
