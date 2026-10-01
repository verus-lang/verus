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

test_verify_one_file! {
    #[test] test_bool_then verus_code! {
        use vstd::prelude::*;

        fn test_then_true() {
            let res: Option<u32> = true.then(|| -> (r: u32) ensures r == 7 { 7 });
            assert(res is Some);
            assert(res->Some_0 == 7);
        }

        fn test_then_false(x: u32) {
            let res: Option<u32> = false.then(|| -> (r: u32)
                requires x < 10
                ensures r == x
            { x });
            assert(res is None);
        }

        fn test_then_conditional(b: bool, x: u32)
            requires b ==> x < 10,
        {
            let res: Option<u32> = b.then(|| -> (r: u32)
                requires x < 10
                ensures r == x
            { x });
            assert(b ==> res is Some);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_bool_then_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let res: Option<u32> = true.then(|| -> (r: u32)
                requires x < 10
                ensures r == x
            { x }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_bool_then_vacuous_closure verus_code! {
        use vstd::prelude::*;

        fn exploit() {
            let f = || -> (z: u8)
                requires false,
                ensures false,
            { 0u8 };
            let o: Option<u8> = true.then(f); // FAILS
            assert(false);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_is_some_and verus_code! {
        use vstd::prelude::*;

        fn test_is_some_and_some() {
            let opt: Option<u32> = Some(4);
            let res: bool = opt.is_some_and(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(res);
        }

        fn test_is_some_and_some_false() {
            let opt: Option<u32> = Some(1);
            let res: bool = opt.is_some_and(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(!res);
        }

        fn test_is_some_and_none() {
            let opt: Option<u32> = None;
            let res: bool = opt.is_some_and(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(!res);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_some_and_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: bool = opt.is_some_and(|y: u32|
                requires y < 10
            { y > 2 }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_is_none_or verus_code! {
        use vstd::prelude::*;

        fn test_is_none_or_some() {
            let opt: Option<u32> = Some(1);
            let res: bool = opt.is_none_or(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(!res);
        }

        fn test_is_none_or_some_true() {
            let opt: Option<u32> = Some(4);
            let res: bool = opt.is_none_or(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(res);
        }

        fn test_is_none_or_none() {
            let opt: Option<u32> = None;
            let res: bool = opt.is_none_or(|x: u32| -> (r: bool)
                ensures r == (x > 2)
            { x > 2 });
            assert(res);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_none_or_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: bool = opt.is_none_or(|y: u32|
                requires y < 10
            { y > 2 }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_unwrap_unchecked verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_unchecked_some() {
            let opt: Option<u32> = Some(42);
            let val: u32 = unsafe { opt.unwrap_unchecked() };
            assert(val == 42);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_unchecked_none verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_unchecked_none() {
            let opt: Option<u32> = None;
            let val: u32 = unsafe { opt.unwrap_unchecked() }; // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_inspect verus_code! {
        use vstd::prelude::*;

        fn test_inspect_some() {
            let opt: Option<u32> = Some(42);
            let res: Option<u32> = opt.inspect(|_x: &u32| {});
            assert(res == Some(42u32));
        }

        fn test_inspect_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.inspect(|_x: &u32| {});
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_inspect_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: Option<u32> = opt.inspect(|y: &u32|
                requires *y < 10
            {}); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_map_or verus_code! {
        use vstd::prelude::*;

        fn test_map_or_some() {
            let opt: Option<u32> = Some(2);
            let res: u32 = opt.map_or(99, |x: u32| -> (r: u32)
                requires x < 1000
                ensures r == x + 1
            { x + 1 });
            assert(res == 3);
        }

        fn test_map_or_none() {
            let opt: Option<u32> = None;
            let res: u32 = opt.map_or(99, |x: u32| -> (r: u32)
                requires x < 1000
                ensures r == x + 1
            { x + 1 });
            assert(res == 99);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_or_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: u32 = opt.map_or(99, |y: u32|
                requires y < 1000
            { y + 1 }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_map_or_else verus_code! {
        use vstd::prelude::*;

        fn test_map_or_else_some() {
            let opt: Option<u32> = Some(2);
            let res: u32 = opt.map_or_else(|| -> (r: u32)
                ensures r == 99
            { 99 }, |x: u32| -> (r: u32)
                requires x < 1000
                ensures r == x + 1
            { x + 1 });
            assert(res == 3);
        }

        fn test_map_or_else_none() {
            let opt: Option<u32> = None;
            let res: u32 = opt.map_or_else(|| -> (r: u32)
                ensures r == 99
            { 99 }, |x: u32| -> (r: u32)
                requires x < 1000
                ensures r == x + 1
            { x + 1 });
            assert(res == 99);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_or_else_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test_default(x: u32) {
            let opt: Option<u32> = None;
            let res: u32 = opt.map_or_else(||
                requires x < 10
            { x }, |y: u32| y); // FAILS
        }

        fn test_map(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: u32 = opt.map_or_else(|| 99, |y: u32|
                requires y < 1000
            { y + 1 }); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] test_copied verus_code! {
        use vstd::prelude::*;

        fn test_copied() {
            let val: u32 = 42;
            let opt: Option<&u32> = Some(&val);
            let res: Option<u32> = opt.copied();
            assert(res == Some(42u32));
        }

        fn test_copied_none() {
            let opt: Option<&u32> = None;
            let res: Option<u32> = opt.copied();
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_and verus_code! {
        use vstd::prelude::*;

        fn test_and_some_some() {
            let opt: Option<u32> = Some(1);
            let res: Option<u32> = opt.and(Some(2));
            assert(res == Some(2u32));
        }

        fn test_and_some_none() {
            let opt: Option<u32> = Some(1);
            let res: Option<u32> = opt.and(None);
            assert(res.is_none());
        }

        fn test_and_none_some() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.and(Some(2));
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_filter verus_code! {
        use vstd::prelude::*;

        fn test_filter_some_true() {
            let opt: Option<u32> = Some(42);
            let res: Option<u32> = opt.filter(|x: &u32| -> (r: bool)
                ensures r == (*x > 10)
            { *x > 10 });
            assert(res == Some(42u32));
        }

        fn test_filter_some_false() {
            let opt: Option<u32> = Some(2);
            let res: Option<u32> = opt.filter(|x: &u32| -> (r: bool)
                ensures r == (*x > 10)
            { *x > 10 });
            assert(res.is_none());
        }

        fn test_filter_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.filter(|x: &u32| -> (r: bool)
                ensures r == (*x > 10)
            { *x > 10 });
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_filter_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = Some(x);
            let res: Option<u32> = opt.filter(|y: &u32|
                requires *y < 10
            { *y > 2 }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_or verus_code! {
        use vstd::prelude::*;

        fn test_or_some() {
            let opt: Option<u32> = Some(1);
            let res: Option<u32> = opt.or(Some(2));
            assert(res == Some(1u32));
        }

        fn test_or_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.or(Some(2));
            assert(res == Some(2u32));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_xor verus_code! {
        use vstd::prelude::*;

        fn test_xor_some_none() {
            let opt: Option<u32> = Some(1);
            let res: Option<u32> = opt.xor(None);
            assert(res == Some(1u32));
        }

        fn test_xor_none_some() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.xor(Some(2));
            assert(res == Some(2u32));
        }

        fn test_xor_some_some() {
            let opt: Option<u32> = Some(1);
            let res: Option<u32> = opt.xor(Some(2));
            assert(res.is_none());
        }

        fn test_xor_none_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.xor(None);
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_or_else verus_code! {
        use vstd::prelude::*;

        fn test_or_else_some() {
            let opt: Option<u32> = Some(42);
            let res: Option<u32> = opt.or_else(|| None);
            assert(res == Some(42u32));
        }

        fn test_or_else_none() {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.or_else(|| -> (r: Option<u32>)
                ensures r == Some(99u32)
            { Some(99) });
            assert(res == Some(99u32));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_or_else_requires_not_satisfied verus_code! {
        use vstd::prelude::*;

        fn test(x: u32) {
            let opt: Option<u32> = None;
            let res: Option<u32> = opt.or_else(||
                requires x < 10
            { Some(x) }); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_replace verus_code! {
        use vstd::prelude::*;

        fn test_replace_some() {
            let mut opt: Option<u32> = Some(5);
            let res: Option<u32> = opt.replace(20);
            assert(res == Some(5u32));
            assert(opt == Some(20u32));
        }

        fn test_replace_none() {
            let mut opt: Option<u32> = None;
            let res: Option<u32> = opt.replace(20);
            assert(res.is_none());
            assert(opt == Some(20u32));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_zip verus_code! {
        use vstd::prelude::*;

        fn test_zip_some_some() {
            let opt: Option<u32> = Some(1);
            let res: Option<(u32, u32)> = opt.zip(Some(2));
            assert(res == Some((1u32, 2u32)));
        }

        fn test_zip_some_none() {
            let opt: Option<u32> = Some(1);
            let res: Option<(u32, u32)> = opt.zip(None);
            assert(res.is_none());
        }

        fn test_zip_none_some() {
            let opt: Option<u32> = None;
            let res: Option<(u32, u32)> = opt.zip(Some(2));
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unzip verus_code! {
        use vstd::prelude::*;

        fn test_unzip_some() {
            let opt: Option<(u32, u32)> = Some((1, 2));
            let res: (Option<u32>, Option<u32>) = opt.unzip();
            assert(res == (Some(1u32), Some(2u32)));
        }

        fn test_unzip_none() {
            let opt: Option<(u32, u32)> = None;
            let res: (Option<u32>, Option<u32>) = opt.unzip();
            assert(res == (None, None));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_flatten verus_code! {
        use vstd::prelude::*;

        fn test_flatten_some_some() {
            let opt: Option<Option<u32>> = Some(Some(42));
            let res: Option<u32> = opt.flatten();
            assert(res == Some(42u32));
        }

        fn test_flatten_some_none() {
            let opt: Option<Option<u32>> = Some(None);
            let res: Option<u32> = opt.flatten();
            assert(res.is_none());
        }

        fn test_flatten_none() {
            let opt: Option<Option<u32>> = None;
            let res: Option<u32> = opt.flatten();
            assert(res.is_none());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_transpose verus_code! {
        use vstd::prelude::*;

        fn test_transpose_some_ok() {
            let opt: Option<Result<u32, u32>> = Some(Ok(42));
            let res: Result<Option<u32>, u32> = opt.transpose();
            assert(res == Ok::<Option<u32>, u32>(Some(42u32)));
        }

        fn test_transpose_some_err() {
            let opt: Option<Result<u32, u32>> = Some(Err(1));
            let res: Result<Option<u32>, u32> = opt.transpose();
            assert(res == Err::<Option<u32>, u32>(1));
        }

        fn test_transpose_none() {
            let opt: Option<Result<u32, u32>> = None;
            let res: Result<Option<u32>, u32> = opt.transpose();
            assert(res == Ok::<Option<u32>, u32>(None));
        }
    } => Ok(())
}
