#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_unwrap_expect verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        proof fn test_option() {
            let ok_option = Option::<i8>::Some(1);
            assert(ok_option is Some);
            assert(ok_option.unwrap() == 1);
            let ok_option2 = Option::<i8>::Some(1);
            assert(ok_option2 is Some);
            assert(ok_option2.expect("option was built with Some") == 1);
            let none_option = Option::<i8>::None;
            assert(none_option is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_ok_or_else verus_code! {
        use vstd::prelude::*;

        fn test_ok_or_else_some() {
            let opt= Some(42);
            let res: Result<u32, u32> = opt.ok_or_else(|| 0);
            assert(res == Ok::<u32, u32>(42));
        }

        fn test_ok_or_else_none() {
            let opt: Option<u32> = None;
            let res: Result<u32, u32> = opt.ok_or_else(|| -> (r: u32)
                ensures r == 99
            { 99 });
            assert(res == Err::<u32, u32>(99));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_or_default verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_or_default_some() {
            let opt: Option<u32> = Some(42);
            let val: u32 = opt.unwrap_or_default();
            assert(val == 42);
        }

        fn test_unwrap_or_default_none() {
            let opt: Option<u32> = None;
            let val: u32 = opt.unwrap_or_default();
            assert(val == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_and_then verus_code! {
        use vstd::prelude::*;

        fn test_and_then_some() {
            let opt: Option<u32> = Some(2);
            let res: Option<u32> = opt.and_then(|x: u32| -> (r: Option<u32>)
                requires x < 1000
                ensures r.is_some() && r.unwrap() == x + 1
            { Some(x + 1) });
            assert(res.is_some());
        }

        fn test_and_then_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.and_then(|x: u32| -> (r: Option<u32>)
                requires x < 1000
                ensures r.is_some() && r.unwrap() == x + 1
            { Some(x + 1) });
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_cloned verus_code! {
        use vstd::prelude::*;

        fn test_cloned() {
            let val: u32 = 42;
            let opt: Option<&u32> = Some(&val);
            let res: Option<u32> = opt.cloned();
            assert(res == Some(42u32));
        }

        fn test_cloned_none() {
            let opt: Option<&u32> = None;
            let res: Option<u32> = opt.cloned();
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_or_else verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_or_else_some() {
            let opt: Option<u32> = Some(42);
            let val: u32 = opt.unwrap_or_else(|| 0);
            assert(val == 42);
        }

        fn test_unwrap_or_else_none() {
            let opt: Option<u32> = None;
            let val: u32 = opt.unwrap_or_else(|| -> (r: u32)
                ensures r == 99
            { 99 });
            assert(val == 99);
        }
    } => Ok(())
}
