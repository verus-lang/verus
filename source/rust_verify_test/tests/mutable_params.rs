#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] mut_param_with_loops [] => verus_code! {
        fn cond() -> bool { true }

        fn test(mut x: u64) -> (y: u64)
            ensures x == y
        {
            let z = x;
            x = 5;
            return z;
        }

        fn test_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 5;
            return 5; // FAILS
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                return x;
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                let z = x;
                x = 5;
                return z; // FAILS (requires invariant relating x to old(x))
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                x = 5;
                return 5; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 1;
            loop {
                let z = x;
                return z; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                if cond() {
                    let z = x;
                    return z; // FAILS
                } else {
                    x = 1;
                }
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mut_param_on_closure_with_loops [] => verus_code! {
        fn cond() -> bool { true }

        fn test() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                let z = x;
                x = 5;
                return z;
            };
        }

        fn test_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 5;
                return 5;
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                loop {
                    return x;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS (requires invariant relating x to old(x))
            {
                loop {
                    let z = x;
                    x = 5;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    x = 5;
                    return 5;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 1;
                loop decreases 0int {
                    let z = x;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    if cond() {
                        let z = x;
                        return z;
                    } else {
                        x = 1;
                    }
                }
            };
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_invariants_spec [] => verus_code! {
        use vstd::prelude::*;

        struct X { }

        impl vstd::invariant::InvariantPredicate<(), ()> for X {
            open spec fn inv(k: (), v: ()) -> bool { true }
        }

        fn open(mut x: u64, Tracked(t): Tracked<&vstd::invariant::AtomicInvariant<(), (), X>>)
            requires t.namespace() == x + 1, x < 10,
            opens_invariants [x]
        {
            x = x + 1;
            vstd::invariant::open_atomic_invariant!(t => i => {
            });
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot show invariant namespace is in the mask given by the scope")
}

test_verify_one_file_with_options! {
    #[test] no_confusion_unwind_spec [] => verus_code! {
        fn panic() { }

        fn open(mut x: u64)
            no_unwind when x != 1
        {
            x = 1;
            panic(); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_ensures_recommend_check [] => verus_code! {
        spec fn rec(x: int) -> bool
            recommends x == 2
        {
            false
        }

        proof fn test_ens(mut x: int)
            ensures rec(x)
        {
            x = 2;
        }
    } => Err(err) => assert_has_recommends_failure(err)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_ensures_recommend_check_closure [] => verus_code! {
        spec fn rec(x: u64) -> bool
            recommends x == 2
        {
            false
        }

        fn test_ens() {
            let r = |mut x: u64|
                ensures rec(x)
            {
                x = 2;
            };
        }
    } => Err(err) => assert_has_recommends_failure(err)
}

test_verify_one_file_with_options! {
    #[test] no_confusion_decreases_clause [] => verus_code! {
        #[allow(unconditional_recursion)]
        fn test(mut x: u64)
            decreases x
        {
            x = 30;
            test(20); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] mut_param_with_loops_iso_false [] => verus_code! {
        fn cond() -> bool { true }

        fn test(mut x: u64) -> (y: u64)
            ensures x == y
        {
            let z = x;
            x = 5;
            return z;
        }

        fn test_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 5;
            return 5; // FAILS
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                return x;
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                let z = x;
                x = 5;
                return z; // FAILS (requires invariant relating x to old(x))
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                x = 5;
                return 5; // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2(mut x: u64) -> (y: u64)
            ensures x == y
        {
            x = 1;
            loop {
                let z = x;
                return z; // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3(mut x: u64) -> (y: u64)
            ensures x == y
        {
            loop {
                if cond() {
                    let z = x;
                    return z; // FAILS
                } else {
                    x = 1;
                }
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mut_param_on_closure_with_loops_iso_false [] => verus_code! {
        fn cond() -> bool { true }

        fn test() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                let z = x;
                x = 5;
                return z;
            };
        }

        fn test_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 5;
                return 5;
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y
            {
                loop {
                    return x;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails0() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS (requires invariant relating x to old(x))
            {
                loop {
                    let z = x;
                    x = 5;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    x = 5;
                    return 5;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails2() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                x = 1;
                loop decreases 0int {
                    let z = x;
                    return z;
                }
            };
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_fails3() {
            let r = |mut x: u64| -> (y: u64)
                ensures x == y // FAILS
            {
                loop {
                    if cond() {
                        let z = x;
                        return z;
                    } else {
                        x = 1;
                    }
                }
            };
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] mutation_conditional_cases [] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test1(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
                loop{}
            } else {
                loop {
                    return x; // ok
                }
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                loop {
                    return x; // ok
                }
            } else {
                x = 20;
                loop{}
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test3(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                loop{}
            } else {
                x = 20;
                loop {
                    return x; // FAILS
                }
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
                loop {
                    return x; // FAILS
                }
            } else {
                loop{}
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test5(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
            } else {
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test6(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
                x = 20;
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test7(mut x: u64) -> (y: u64)
            ensures y == x
        {
            if cond() {
            } else {
                x = 20;
            }

            loop {
                return x; // FAILS
            }
        }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test8(mut x: u64) -> (y: u64)
            ensures y == x
        {
            x = 20;

            if cond() {
            } else {
            }

            loop {
                return x; // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] mutation_nested_loop [] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::loop_isolation(true)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test(mut x: u64) -> (y: u64)
            ensures y == x
        {
            loop {
                if cond() {
                    return x; // FAILS
                }

                loop {
                    if cond() {
                        x = 20;
                    }
                    if cond() {
                        break;
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

// https://github.com/verus-lang/verus/issues/1933
// An ident subpattern (`a @ b: T`) in parameter position used to silently
// register only the outer name (`a`), leaving `b` unregistered - referencing
// `b` in the body then panicked in mode-checking instead of being rejected
// here with a clear error.
test_verify_one_file_with_options! {
    #[test] ident_subpattern_in_param_position_rejected_not_panicking [] => verus_code! {
        fn double(a @ b: i32) -> i32 { a + b }
    } => Err(err) => assert_vir_error_msg(err, "plain identifier pattern")
}

// A more useful shape than the plain identifier-alias repro above: the
// subpattern here is a real destructure (`(a, b)`), not just another name -
// this hits the same underlying bug (pat_to_mut_var silently drops the
// subpattern regardless of what it is), so it must be rejected the same way
// rather than only handling the trivial ident-only case from the issue.
test_verify_one_file_with_options! {
    #[test] tuple_destructure_at_pattern_in_param_position_rejected_not_panicking [] => verus_code! {
        fn process(whole @ (a, b): (i32, i32)) -> i32 { a + b + whole.0 }
    } => Err(err) => assert_vir_error_msg(err, "plain identifier pattern")
}

test_verify_one_file_with_options! {
    #[test] tuple_pattern_in_param_position_rejected [] => verus_code! {
        fn add_pair((a, b): (i32, i32)) -> i32 { a + b }
    } => Err(err) => assert_vir_error_msg(err, "plain identifier pattern")
}

test_verify_one_file_with_options! {
    #[test] wildcard_pattern_in_param_position [] => code! {
        #[verifier::verify]
        fn ignore_arg(_: bool, value: i32, _: u64) -> i32 {
            ensures(|result: i32| [result == value]);
            value
        }

        verus! {
            fn caller() {
                let result = ignore_arg(true, 10, 20);
                assert(result == 10);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_named_returns [] => verus_code! {
        fn f<T>(_: T, value: u32, _: &mut u64) -> (result: u32)
            ensures result == value
        {
            value
        }

        fn g(_: impl Sized, _: &impl Sized) -> (result: (impl Sized, bool))
            ensures result.1
        {
            (true, true)
        }

        fn caller() {
            let mut value = 30u64;
            let result = f(false, 20, &mut value);
            assert(result == 20);
            let result = g(true, &false);
            assert(result.1);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_params_preserve_spec_and_proof_modes [] => verus_code! {
        spec fn zero(_: int) -> int { 0 }
        proof fn ignore_ghost(_: int) {}
        proof fn ignore_tracked<T>(tracked _: T) -> (result: bool)
            ensures result
        {
            true
        }

        proof fn caller<T>(tracked token: T) {
            ignore_ghost(10);
            let result = ignore_tracked(token);
            assert(result);
            assert(zero(20) == 0);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_tracked_consumes_token [] => verus_code! {
        proof fn ignore<T>(tracked _: T) {}

        proof fn caller<T>(tracked token: T) {
            ignore(token);
            ignore(token);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value")
}

test_verify_one_file_with_options! {
    #[test] wildcard_params_named_return_false_postcondition [] => verus_code! {
        fn f(_: impl Sized) -> (result: (impl Sized, bool))
            ensures result.1 // FAILS
        {
            (true, false)
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] wildcard_params_async_named_returns ["vstd"] => code! {
        use vstd::prelude::*;

        verus! {
            async fn ignore(_: u32) -> (result: bool)
                ensures result
            {
                true
            }
        }

        #[verus_spec(result => ensures result)]
        async fn ignore_attr(_: u32) -> bool {
            true
        }

        verus! {
            async fn caller() {
                let result = ignore(10).await;
                assert(result);
                let result = ignore_attr(20).await;
                assert(result);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_name_hygiene [] => code! {
        const __verus_wildcard_param_0: u32 = 0;
        struct __verus_wildcard_param_1;

        verus! {
            fn f(_: u32, _: bool) -> (r: u32)
                ensures r == 1
            {
                fn __verus_wildcard_param_0() -> bool { true }
                1
            }
        }

        #[verus_spec(r => ensures r == 1)]
        fn g(_: u32, _: bool) -> u32 {
            fn __verus_wildcard_param_0() -> bool { true }
            1
        }

        verus! {
            fn caller() {
                let r = f(5, true);
                assert(r == 1);
                let r = g(5, true);
                assert(r == 1);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_params_in_trait_methods_and_external_body [] => verus_code! {
        trait Ignore {
            fn mixed(&self, _: bool, value: u32, _: u64) -> (result: u32)
                ensures result == value;
        }

        struct S;

        impl Ignore for S {
            fn mixed(&self, _: bool, value: u32, _: u64) -> u32 {
                value
            }
        }

        #[verifier::external_body]
        fn external(_: u32) -> (result: bool)
            ensures result
        {
            true
        }

        fn caller() {
            let result = S.mixed(false, 20, 30);
            assert(result == 20);
            let result = external(40);
            assert(result);
        }
    } => Ok(())
}
