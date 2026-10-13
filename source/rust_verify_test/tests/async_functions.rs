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
    } => Err(err) => assert_vir_error_msg(err, "async is only supported for 'exec' functions")
}

test_verify_one_file! {
    #[test] async_proof_fn verus_code! {
        async proof fn foo() -> bool {
            true
        }
    } => Err(err) => assert_vir_error_msg(err, "async is only supported for 'exec' functions")
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

test_verify_one_file! {
    #[test] async_with_mismatch_type code! {
        #[verus::internal(verus_macro)]
        async fn foo() -> u64 {
            ::vstd::prelude::ensures(|ret: u32|
                    [::vstd::prelude::spec_eq(ret, 3u64)]);
            return 3;
        }
    } => Err(err) => assert_vir_error_msg(err, "return type does not match binder in ensures")
}
