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

test_verify_one_file_with_options! {
    #[test] patterns_in_param_position_without_macro [] => code! {
        #[verus::internal(verify)]
        fn add_pair((a, b): (i32, i32)) -> i32 {
            requires(a == 1 && b == 2);
            ensures(|result: i32| [result == a + b]);
            a + b
        }

        #[verus::internal(verify)]
        fn ignore_arg(_: bool, value: i32, _: u64) -> i32 {
            ensures(|result: i32| [result == value]);
            value
        }

        verus! {
            fn caller() {
                let r = add_pair((1, 2));
                assert(r == 3);
                let result = ignore_arg(true, 10, 20);
                assert(result == 10);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] param_patterns ["vstd", "--compile"] => verus_code! {
        fn first((x, _): (u32, u32)) -> (r: u32)
            ensures r == x
        {
            x
        }

        fn swap<A, B>((a, b): (A, B)) -> (r: (B, A))
            ensures r.0 == b && r.1 == a
        {
            (b, a)
        }

        struct P { a: u64, b: u64 }
        struct W(u64, u64);
        struct V(u32);

        fn nested(((a, b), P { a: c, .. }, W(d, _)): ((u8, u8), P, W)) -> (r: u64)
            requires c < 10, d < 10
            ensures r == a + b + c + d
        {
            a as u64 + b as u64 + c + d
        }

        fn single(V(x): V) -> (r: u32)
            ensures r == x
        {
            x
        }

        fn refs(&(x, y): &(u32, u32)) -> (r: u32)
            requires x < 100, y < 100
            ensures r == x + y
        {
            x + y
        }

        fn mutate((mut x, y): (u32, u32)) -> (r: u32)
            ensures r == y
        {
            x = y;
            x
        }

        fn by_ref(ref x: u32, ref s: String) -> (r: u32)
            ensures r == *x
        {
            *x
        }

        fn wildcards<T>(_: T, value: u32, _: &mut u64) -> (r: u32)
            ensures r == value
        {
            value
        }

        fn opaque(_: impl Sized, _: &impl Sized) -> (r: (impl Sized, bool))
            ensures r.1
        {
            (true, true)
        }

        #[verifier::external_body]
        fn external_body((s, t): (String, String)) -> (r: String)
            ensures r == s
        {
            let _ = t;
            s
        }

        #[verifier::external]
        fn external((s, t): (String, String)) -> (r: String)
            ensures r == s
        {
            let _ = t;
            s
        }

        fn caller() {
            let r = first((1, 2));
            assert(r == 1);
            let r = swap((1u8, true));
            assert(r.0 && r.1 == 1);
            let r = nested(((1, 2), P { a: 3, b: 0 }, W(4, 9)));
            assert(r == 10);
            let r = single(V(3));
            assert(r == 3);
            let r = refs(&(5, 6));
            assert(r == 11);
            let mut value = 30u64;
            let r = wildcards(false, 20, &mut value);
            assert(r == 20);
            let r = opaque(true, &false);
            assert(r.1);
        }

        fn double(a @ b: i32) -> (r: i32)
            requires -100 < a < 100
            ensures r == 2 * a
        {
            a + b
        }

        fn process(mut whole @ (a, b): (i32, i32)) -> (r: i32)
            requires whole.0 == 1, b == 2
            ensures r == 4
        {
            whole.0 = whole.0 + a;
            whole.0 + b
        }

        fn incr(x @ _: &mut u32)
            requires *old(x) < 100
            ensures *final(x) == *old(x) + 1
        {
            *x = *x + 1;
        }

        spec fn sum((a, b): (nat, nat)) -> nat
            decreases a
        {
            if a == 0 { b } else { sum(((a - 1) as nat, b)) }
        }

        spec fn zero(_: int) -> int { 0 }

        proof fn lemma((a, b): (nat, nat))
            ensures sum((a, b)) >= b
            decreases a
        {
            if a > 0 {
                lemma(((a - 1) as nat, b));
            }
        }

        proof fn split<A, B>(tracked (a, b): (A, B)) -> (tracked r: A)
            ensures r == a
        {
            a
        }

        proof fn ignore_ghost(_: int) {}

        proof fn ignore_tracked<T>(tracked _: T) -> (r: bool)
            ensures r
        {
            true
        }

        proof fn proof_caller<T>(tracked token: T) {
            ignore_ghost(10);
            let r = ignore_tracked(token);
            assert(r);
            assert(zero(20) == 0);
        }

        fn opens((x, _): (u32, u32))
            opens_invariants none
            no_unwind when x > 0
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] param_patterns_false_postcondition [] => verus_code! {
        fn first((x, _): (u32, u32)) -> (r: u32)
            ensures r == x + 1 // FAILS
        {
            x
        }

        fn opaque(_: impl Sized) -> (r: (impl Sized, bool))
            ensures r.1 // FAILS
        {
            (true, false)
        }
    } => Err(err) => assert_fails(err, 2)
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
    #[test] param_patterns_async ["vstd"] => code! {
        use vstd::prelude::*;

        verus! {
            async fn ignore(_: String) -> (r: bool)
                ensures r
            {
                true
            }

            async fn ignore_at(x @ _: u32) -> (r: u32)
                ensures r == x
            {
                x
            }
        }

        #[verus_spec(r => ensures r)]
        async fn ignore_attr(_: String) -> bool {
            true
        }

        verus! {
            async fn caller(s: String, t: String) {
                let r = ignore(s).await;
                assert(r);
                let r = ignore_attr(t).await;
                assert(r);
                let r = ignore_at(5).await;
                assert(r == 5);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] wildcard_params_in_trait_methods [] => code! {
        #[verus::internal(verify)]
        trait Plain {
            fn m(&self, _: u32, _: u32);
        }

        verus! {
            trait T {
                fn m(&self, _: u32, __verus_param_1: u32) -> (r: u32)
                    ensures r == __verus_param_1;
            }

            struct S;

            impl T for S {
                fn m(&self, _: u32, x: u32) -> u32 {
                    x
                }
            }

            fn caller() {
                let r = S.m(1, 2);
                assert(r == 2);
            }
        }

        trait A {
            #[verus_spec(r => ensures r == __verus_param_1)]
            fn m(&self, _: u32, __verus_param_1: u32) -> u32;
        }
    } => Ok(())
}

// The generated names can't clash with user items ...
test_verify_one_file_with_options! {
    #[test] param_name_hygiene_items [] => code! {
        const __verus_param_0: u32 = 0;
        struct __verus_param_1;

        verus! {
            fn f(_: u32, _: bool) -> (r: u32)
                ensures r == 1
            {
                fn __verus_param_0() -> bool { true }
                1
            }
        }

        #[verus_spec(r => ensures r == 1)]
        fn g(_: u32, _: bool) -> u32 {
            fn __verus_param_0() -> bool { true }
            1
        }
    } => Ok(())
}

// ... or with user variables
test_verify_one_file_with_options! {
    #[test] param_name_hygiene_variables [] => code! {
        verus! {
            fn f(_: u32, _: u32, __verus_param_0: u32) -> (__verus_param_1: u32)
                ensures __verus_param_1 == __verus_param_0
            {
                let __verus_param_x @ (a, b) = (__verus_param_0, 0u32);
                __verus_param_x.0
            }
        }

        #[verus_spec(__verus_param_1 => ensures __verus_param_1 == __verus_param_0)]
        fn g(_: u32, _: u32, __verus_param_0: u32) -> u32 {
            let __verus_param_x @ (a, b) = (__verus_param_0, 0u32);
            __verus_param_x.0
        }

        verus! {
            fn param_binder(__verus_param_x @ (a, b): (u32, u32)) -> (r: u32)
                ensures r == a
            {
                __verus_param_x.0
            }

            fn ref_binder(ref __verus_param_x: u32) -> (r: u32)
                ensures r == *__verus_param_x
            {
                *__verus_param_x
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] param_patterns_async_unsupported [] => verus_code! {
        async fn f(x @ (a, b): (u32, u32)) -> u32 {
            a
        }

        async fn g((x, _): (u32, u32)) -> (r: u32)
            ensures r == x
        {
            x
        }
    } => Err(err) => assert_vir_error_msgs(err, &[
        "patterns in async function parameters are not supported",
        "patterns in async function parameters are not supported",
    ])
}

test_verify_one_file_with_options! {
    #[test] param_patterns_unsupported [] => verus_code! {
        fn f<A, B>(tracked (a, b): (A, B)) {}

        fn g((x, y): &mut (u64, u64)) {}
    } => Err(err) => assert_vir_error_msgs(err, &[
        "patterns in ghost or tracked parameters of exec functions are not supported",
        "Verus does not currently support `ref mut` bindings in parameters",
    ])
}

test_verify_one_file_with_options! {
    #[test] wildcard_param_assume_specification_unsupported [] => verus_code! {
        #[verifier::external]
        fn foo(x: u32) -> u32 {
            x
        }

        pub assume_specification[foo](_: u32) -> u32;
    } => Err(err) => assert_vir_error_msg(err, "'assume_specification' expects ident, not complex pattern")
}
