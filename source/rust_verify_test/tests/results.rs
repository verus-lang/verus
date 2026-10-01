#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_result verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        // Result::unwrap and Result::unwrap_err require trait bounds

        use core::fmt::Debug;

        #[verifier::external]
        impl Debug for Err {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                unimplemented!();
            }
        }

        proof fn test_result() {
            let ok_result = Result::<i8, Err>::Ok(1);
            assert(ok_result is Ok);
            assert(ok_result.unwrap() == 1);
            let err_result = Result::<i8, Err>::Err(Err{ error_code: -1 });
            assert(err_result is Err);
            assert(err_result->Err_0 == Err{ error_code: -1 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_result_fails verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        proof fn test_ok_result() {
            let ok_result = Result::<int, Err>::Ok(1);
            assert(ok_result is Err); // FAILS
        }

        proof fn test_err_result() {
            let err_result = Result::<int, Err>::Err(Err{ error_code: -1 });
            assert(err_result is Ok); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] test_result_expect verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        // Result::unwrap and Result::unwrap_err require trait bounds

        use core::fmt::Debug;

        #[verifier::external]
        impl Debug for Err {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                unimplemented!();
            }
        }

        proof fn test_result() {
            let ok_result = Result::<i8, Err>::Ok(1);
            assert(ok_result is Ok);
            assert(ok_result.expect("the result is ok") == 1);
            let err_result = Result::<i8, Err>::Err(Err{ error_code: -1 });
            assert(err_result is Err);
            assert(err_result->Err_0 == Err{ error_code: -1 });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_unchecked verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_unchecked_ok() {
            let r: Result<u32, u8> = Ok(42);
            let val: u32 = unsafe { r.unwrap_unchecked() };
            assert(val == 42);
        }

        fn test_unwrap_err_unchecked_err() {
            let r: Result<u32, u8> = Err(7);
            let e: u8 = unsafe { r.unwrap_err_unchecked() };
            assert(e == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_expect_err verus_code! {
        use vstd::prelude::*;

        fn test_expect_err_err() {
            let r: Result<u32, u8> = Err(7);
            let e: u8 = r.expect_err("result was built with Err");
            assert(e == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_or verus_code! {
        use vstd::prelude::*;

        fn test_map_or_ok() {
            let r: Result<u32, u8> = Ok(2);
            let val: u32 = r.map_or(0, |x: u32| -> (y: u32)
                requires x < 1000
                ensures y == x + 1
            { x + 1 });
            assert(val == 3);
        }

        fn test_map_or_err() {
            let r: Result<u32, u8> = Err(1);
            let val: u32 = r.map_or(7, |x: u32| -> (y: u32)
                requires x < 1000
            { x + 1 });
            assert(val == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_map_or_else verus_code! {
        use vstd::prelude::*;

        fn test_map_or_else_ok() {
            let r: Result<u32, u8> = Ok(2);
            let val: u32 = r.map_or_else(|e: u8| 0, |x: u32| -> (y: u32)
                requires x < 1000
                ensures y == x + 1
            { x + 1 });
            assert(val == 3);
        }

        fn test_map_or_else_err() {
            let r: Result<u32, u8> = Err(1);
            let val: u32 = r.map_or_else(|e: u8| -> (y: u32)
                ensures y == e as u32
            { e as u32 }, |x: u32| 0);
            assert(val == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_and_then verus_code! {
        use vstd::prelude::*;

        fn test_and_then_ok() {
            let r: Result<u32, u8> = Ok(2);
            let res: Result<u32, u8> = r.and_then(|x: u32| -> (y: Result<u32, u8>)
                requires x < 1000
                ensures y is Ok && y->Ok_0 == x + 1
            { Ok(x + 1) });
            assert(res == Ok::<u32, u8>(3));
        }

        fn test_and_then_err() {
            let r: Result<u32, u8> = Err(1);
            let res: Result<u32, u8> = r.and_then(|x: u32| -> (y: Result<u32, u8>)
                requires x < 1000
            { Ok(x + 1) });
            assert(res == Err::<u32, u8>(1));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_or_else verus_code! {
        use vstd::prelude::*;

        fn test_or_else_ok() {
            let r: Result<u32, u8> = Ok(2);
            let res: Result<u32, u8> = r.or_else(|e: u8| Err(e));
            assert(res == Ok::<u32, u8>(2));
        }

        fn test_or_else_err() {
            let r: Result<u32, u8> = Err(1);
            let res: Result<u32, u8> = r.or_else(|e: u8| -> (y: Result<u32, u8>)
                ensures y == Ok::<u32, u8>(e as u32)
            { Ok(e as u32) });
            assert(res == Ok::<u32, u8>(1));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_or_else verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_or_else_ok() {
            let r: Result<u32, u8> = Ok(42);
            let val: u32 = r.unwrap_or_else(|e: u8| 0);
            assert(val == 42);
        }

        fn test_unwrap_or_else_err() {
            let r: Result<u32, u8> = Err(1);
            let val: u32 = r.unwrap_or_else(|e: u8| -> (y: u32)
                ensures y == 99
            { 99 });
            assert(val == 99);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_is_ok_and verus_code! {
        use vstd::prelude::*;

        fn test_is_ok_and() {
            let r: Result<u32, u8> = Ok(2);
            let b: bool = r.is_ok_and(|x: u32| -> (b: bool)
                ensures b == (x > 1)
            { x > 1 });
            assert(b);
            let r: Result<u32, u8> = Err(1);
            let b: bool = r.is_ok_and(|x: u32| true);
            assert(!b);
        }

        fn test_is_err_and() {
            let r: Result<u32, u8> = Err(1);
            let b: bool = r.is_err_and(|e: u8| -> (b: bool)
                ensures b == (e == 1)
            { e == 1 });
            assert(b);
            let r: Result<u32, u8> = Ok(2);
            let b: bool = r.is_err_and(|e: u8| true);
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_inspect verus_code! {
        use vstd::prelude::*;

        fn test_inspect() {
            let r: Result<u32, u8> = Ok(2);
            let res: Result<u32, u8> = r.inspect(|_x: &u32| {});
            assert(res == Ok::<u32, u8>(2));
        }

        fn test_inspect_err() {
            let r: Result<u32, u8> = Err(1);
            let res: Result<u32, u8> = r.inspect_err(|_e: &u8| {});
            assert(res == Err::<u32, u8>(1));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_and_or verus_code! {
        use vstd::prelude::*;

        fn test_and_or() {
            let ok: Result<u32, u8> = Ok(1);
            let err: Result<u32, u8> = Err(2);
            assert(ok.and(err) == err);
            assert(err.and(ok) == err);
            assert(ok.or(err) == ok);
            assert(err.or(ok) == ok);
        }

        proof fn test_and_or_spec() {
            let ok = Result::<u32, u8>::Ok(1);
            let err = Result::<u32, u8>::Err(2);
            assert(ok.and(err) == err);
            assert(ok.or(err) == ok);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_or verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_or() {
            let r: Result<u32, u8> = Ok(42);
            assert(r.unwrap_or(0) == 42);
            let r: Result<u32, u8> = Err(1);
            assert(r.unwrap_or(0) == 0);
        }

        proof fn test_unwrap_or_spec() {
            let r = Result::<u32, u8>::Err(1);
            assert(r.unwrap_or(9) == 9);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_flatten verus_code! {
        use vstd::prelude::*;

        fn test_flatten() {
            let r: Result<Result<u32, u8>, u8> = Ok(Err(1));
            assert(r.flatten() == Err::<u32, u8>(1));
            let r: Result<Result<u32, u8>, u8> = Err(2);
            assert(r.flatten() == Err::<u32, u8>(2));
        }

        proof fn test_flatten_spec() {
            let r = Result::<Result<u32, u8>, u8>::Ok(Ok(3));
            assert(r.flatten() == Ok::<u32, u8>(3));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_transpose verus_code! {
        use vstd::prelude::*;

        fn test_transpose() {
            let r: Result<Option<u32>, u8> = Ok(Some(4));
            assert(r.transpose() == Some(Ok::<u32, u8>(4)));
            let r: Result<Option<u32>, u8> = Ok(None);
            assert(r.transpose() is None);
            let r: Result<Option<u32>, u8> = Err(5);
            assert(r.transpose() == Some(Err::<u32, u8>(5)));
        }

        proof fn test_transpose_spec() {
            let r = Result::<Option<u32>, u8>::Ok(None);
            assert(r.transpose() is None);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_unwrap_or_default verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_or_default_ok() {
            let r: Result<u32, u8> = Ok(42);
            let val: u32 = r.unwrap_or_default();
            assert(val == 42);
        }

        fn test_unwrap_or_default_err() {
            let r: Result<u32, u8> = Err(1);
            let val: u32 = r.unwrap_or_default();
            assert(val == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_result_combinators_fails verus_code! {
        use vstd::prelude::*;

        fn test_unwrap_unchecked_err() {
            let r: Result<u32, u8> = Err(1);
            let val: u32 = unsafe { r.unwrap_unchecked() }; // FAILS
        }

        fn test_expect_err_ok() {
            let r: Result<u32, u8> = Ok(1);
            let e: u8 = r.expect_err("result was built with Ok"); // FAILS
        }

        fn test_map_or_requires_not_satisfied() {
            let r: Result<u32, u8> = Ok(2);
            let val: u32 = r.map_or(0, |x: u32| -> (y: u32)
                requires x < 1
            { x }); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
