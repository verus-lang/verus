#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_basic_async_function_tracked_variable_pass verus_code! {
        use vstd::prelude::*;

        async fn bar()
        {}

        async fn reference_ok()
        {
            let tracked t = 1usize;
            let tracked t_ref = &t;
            bar().await;
        }

        async fn mut_reference_ok()
        {
            let tracked mut t = 1usize;
            let tracked t_ref = &mut t;
            bar().await;
        }

        async fn move_ok()
        {
            let tracked mut t = 1usize;
            let tracked t_ref = &mut t;
            bar().await;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_tracked_variable_reference_fail verus_code! {
        use vstd::prelude::*;

        async fn bar()
        {}

        async fn reference_fail()
        {
            let tracked t = 1usize;
            bar().await;
            let tracked t_ref = &t;
        }
    } => Err(err) => assert_vir_error_msg(err, "a tracked variable `t` is alive, across an `await` point, which is not currently supported in an async function, please wrap it in Tracked<> to work around it")
}

test_verify_one_file! {
    #[test] test_basic_async_function_tracked_variable_mut_reference_fail verus_code! {
        use vstd::prelude::*;

        async fn bar()
        {}

        async fn mut_reference_fail()
        {
            let tracked mut t = 1usize;
            bar().await;
            let tracked t_ref = &mut t;
        }
    } => Err(err) => assert_vir_error_msg(err, "a tracked variable `t` is alive, across an `await` point, which is not currently supported in an async function, please wrap it in Tracked<> to work around it")
}

test_verify_one_file! {
    #[test] test_basic_async_function_tracked_variable_move_fail verus_code! {
        use vstd::prelude::*;

        async fn bar()
        {}

        async fn move_fail()
        {
            let tracked mut t = 1usize;
            bar().await;
            let tracked t_ref = t;
        }
    } => Err(err) => assert_vir_error_msg(err, "a tracked variable `t` is alive, across an `await` point, which is not currently supported in an async function, please wrap it in Tracked<> to work around it")
}

test_verify_one_file! {
    #[test] test_basic_async_function_tracked_variable_move_proof_mode_fail verus_code! {
        use vstd::prelude::*;

        async fn bar()
        {}

        proof fn consume(x: usize)
        {}

        async fn consume_fail()
        {
            let tracked t = 1usize;
            bar().await;
            proof {
                consume(t);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "a tracked variable `t` is alive, across an `await` point, which is not currently supported in an async function, please wrap it in Tracked<> to work around it")
}

test_verify_one_file! {
    #[test] test_basic_async_function_auto_trait_ok verus_code! {
        use vstd::prelude::*;
        pub fn consumes_opaque<F>(f: F)
            where
            F: Send,
        {}
        pub async fn ret233<T>(t:T) -> (res: usize)
        {
            233
        }
        pub async fn test_consume_opaque(){
            let f = ret233(1usize);
            consumes_opaque(f);
        }
    } => Ok(_)
}

test_verify_one_file! {
    #[test] test_basic_external_async_function_auto_trait_ok verus_code! {
        use vstd::prelude::*;
        pub fn consumes_opaque<F>(f: F)
            where
            F: Send,
        {}
        #[verifier(external_fn_specification)]
        pub async fn ret233_requires_ensures<T>(t:T) -> (res: usize)
        {
            ret233(t).await
        }
        #[verifier(external)]
        pub async fn ret233<T>(t:T) -> (res: usize)
        {
            233
        }
        pub async fn test_consume_opaque(){
            let f = ret233(1usize);
            consumes_opaque(f);
        }
    } => Ok(_)
}
