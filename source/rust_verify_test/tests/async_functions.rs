#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_pass verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 2,  // FAILS
        {
            1
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_basic_async_function_and_await verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let future = foo();
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_util verus_code! {
        use vstd::prelude::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let future = foo();
            assert(future.awaited() ==> future@ == 1);
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_lifetime_fail verus_code! {
        use vstd::prelude::*;
        async fn foo(x :&usize) -> (ret: usize)
            ensures
                ret == 1,
        {
            1
        }
        async fn bar() {
            let mut x = 233;
            let future = foo(&x);
            x = 2333;
            let ret = future.await;
            x = 2333;
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}

test_verify_one_file! {
    #[test] test_basic_async_function_nested_pass verus_code! {
        use vstd::prelude::*;
        use core::future::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 233,
        {
            233
        }

        async fn foo_of_foo() -> (ret: impl Future<Output = usize>)
            ensures
                ret.awaited() ==> ret@ == 233,
        {
            foo()
        }
        async fn bar() {
            let future_of_future = foo_of_foo();
            let ret = future_of_future.await.await;
            assert(ret == 233);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_await_outside_of_async_function_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                ret == 233,
        {
            233
        }

        fn bar() {
            let future = foo();
            future.await;
        }
    } => Err(err) => assert_rust_error_msg(err, "`await` is only allowed inside `async` functions and blocks")
}

test_verify_one_file! {
    #[test] test_async_function_external_specification verus_code! {
        use vstd::prelude::*;
        #[verifier(external)]
        async fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        async fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures ret_b == !b
        {
            negate_bool(b, x).await
        }

        async fn foo(){
            let future = negate_bool(true, 1);
            let ret = future.await;
            assert(ret == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_function_mut_ref_ok verus_code! {
        use vstd::prelude::*;
        pub async fn bar(x: &mut usize) -> (ret: ())
            ensures
                *final(x) == 2333,
        {
            *x = 2333;
        }

        async fn foo(){
            let mut x = 233;
            let future = bar(&mut x);
            future.await;
            assert(x == 2333);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] unit_return_value_issue2321 verus_code! {
        use vstd::prelude::*;
        async fn set_zero(x: &mut usize)
            ensures *final(x) == 0,
        {
            *x = 0;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] async_impl_future_trait_issue2521 code! {
        use std::future::Future;
        use vstd::prelude::*;

        trait T {
            fn f() -> impl Future;
        }

        struct S;

        impl T for S {
          fn f() -> impl Future { async {} }
        }

        verus! {
          async fn foo();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] async_spec_fn verus_code! {
        async spec fn foo() -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "async is only supported for `exec` functions")
}

test_verify_one_file! {
    #[test] async_proof_fn verus_code! {
        async proof fn foo() -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "async is only supported for `exec` functions")
}

test_verify_one_file! {
    #[test] async_with_returns verus_code! {
        use vstd::prelude::*;

        async fn foo() -> (ret: u64)
            returns 3u64
        {
            return 3;
        }

        async fn foo_fails() -> (ret: u64)
            returns 3u64
        {
            return 4; // FAILS
        }

        async fn get_foo() {
            let f = foo().await;
            assert(f == 3);
        }

        async fn get_foo_fails() {
            let f = foo().await;
            assert(f == 4); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] async_with_allow_in_spec verus_code! {
        spec fn foo_spec() -> u64 {
            3
        }

        #[verifier::allow_in_spec]
        async fn foo() -> (ret: u64)
            returns 3u64
        {
            return 3;
        }
    } => Err(err) => assert_vir_error_msg(err, "async is not supported together with `allow_in_spec`")
}

test_verify_one_file_with_options! {
    #[test] async_with_mismatch_type ["--allow-hand-written-internal-attrs"] => code! {
        #[verus::internal(verus_macro)]
        async fn foo() -> u64 {
            ::vstd::prelude::ensures(|ret: u32|
                    [::vstd::prelude::spec_eq(ret, 3u64)]);
            return 3;
        }
    } => Err(err) => assert_vir_error_msg(err, "return type does not match binder in ensures")
}

test_verify_one_file! {
    #[test] hir_typeck_depends_on_borrowck_issue2323 verus_code! {
        use vstd::prelude::*;
        use std::future::Future;

        pub fn consumes_opaque<F>(f: F)
            where
            F: Future<Output = usize> + Send,
        {}

        async fn ret42() -> (res: usize)
        {
            42
        }
        async fn verified_join_set_client() {
            let f1 = ret42();
            consumes_opaque(f1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] hir_typeck_depends_on_borrowck_type_error verus_code! {
        use vstd::prelude::*;
        use std::future::Future;

        pub fn consumes_opaque<F>(f: F)
            where
            F: Future<Output = usize> + Send,
        {}

        async fn ret42() -> (res: usize)
        {
            42u64
        }
        async fn verified_join_set_client() {
            let f1 = ret42();
            consumes_opaque(f1);
        }
    } => Err(err) => {
        assert!(err.errors.len() == 2);
        assert!(err.errors[0].message.contains("mismatched types"));
        assert!(err.errors[1].message.contains("type-checking error"));
    }
}

test_verify_one_file! {
    #[test] hir_typeck_depends_on_borrowck_marker_trait_error verus_code! {
        use vstd::prelude::*;
        use std::future::Future;
        use std::rc::Rc;

        pub fn consumes_opaque<F>(f: F)
            where
            F: Future<Output = usize> + Send,
        {}

        async fn moo() { }

        fn consume(x: Rc<u64>) { }

        async fn ret42() -> (res: usize)
        {
            let x = Rc::new(20); // not a Send type
            moo().await;
            consume(x);
            42
        }

        async fn verified_join_set_client() {
            let f1 = ret42();
            consumes_opaque(f1);
        }
    } => Err(err) => assert_vir_error_msg(err, "future cannot be sent between threads safely")
}

test_verify_one_file! {
    #[test] hir_typeck_depends_on_borrowck_marker_trait_error_tracked verus_code! {
        use vstd::prelude::*;
        use std::future::Future;
        use std::rc::Rc;

        pub fn consumes_opaque<F>(f: F)
            where
            F: Future<Output = usize> + Send,
        {}

        async fn moo() { }

        axiom fn get_rc() -> (tracked r: Rc<u64>);
        proof fn consume(tracked x: Rc<u64>) { }

        async fn ret42() -> (res: usize)
        {
            let tracked x = get_rc(); // not a Send type
            moo().await;
            proof { consume(x); }
            42
        }

        async fn verified_join_set_client() {
            let f1 = ret42();
            consumes_opaque(f1);
        }
    } => Err(err) => assert_vir_error_msg(err, "future cannot be sent between threads safely")
}

test_verify_one_file! {
    #[test] opaque_type_with_anon_consts verus_code! {
        use vstd::prelude::*;
        use std::future::Future;

        pub fn consumes_opaque<'a, F>(f: F)
            where
            F: Future<Output = usize> + Send
        {}

        async fn ret42(r: &usize) -> (res: usize)
        {
            *r
        }

        async fn caller() {
            let j = 5;
            let f1 = ret42(&j);
            // The presence of the anonymous const (the 2 in the array type)
            // can cause dependency ordering issues if we aren't careful.
            let r: [u64; 2] = [0, 1];
            consumes_opaque(f1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] opaque_type_with_anon_consts_fail verus_code! {
        use vstd::prelude::*;
        use std::future::Future;

        spec const N: usize = 5;

        pub fn consumes_opaque<'a, F>(f: F)
            where
            F: Future<Output = usize> + Send
        {}

        async fn ret42(r: &usize) -> (res: usize)
        {
            *r
        }

        async fn caller() {
            let j = 5;
            let f1 = ret42(&j);
            // The presence of the anonymous const (the 2 in the array type)
            // can cause dependency ordering issues if we aren't careful.
            // The dependency issues are related to this particular mode-checking error,
            // so this test is here to ensure the mode-checking error still fires
            // even in the presence of the opaque type dependency scenario.
            let r = [0u8; core::mem::size_of_val(&N)];
            consumes_opaque(f1);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}
