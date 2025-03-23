#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] normal_fn_requires_fail ["-V check-api-safety"] => verus_code! {
        pub fn test(x: u8)
            requires x > 0,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] normal_fn_private_is_ok ["-V check-api-safety"] => verus_code! {
        fn test(x: u8)
            requires x > 0,
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] normal_fn_unsafe_is_ok ["-V check-api-safety"] => verus_code! {
        pub unsafe fn test(x: u8)
            requires x > 0,
        {
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] normal_fn_ensures_is_ok ["-V check-api-safety"] => verus_code! {
        pub fn test(x: u8) -> (y: u8)
            ensures y > 0
        {
            20
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] normal_fn_mask_is_ok ["-V check-api-safety"] => verus_code! {
        pub fn test(x: u8) -> (y: u8)
            opens_invariants none
        {
            20
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] normal_fn_unwind_is_ok ["-V check-api-safety"] => verus_code! {
        pub fn test(x: u8) -> (y: u8)
            no_unwind
        {
            20
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] trait_fn_requires_is_ok ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8)
                requires x == 0;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] trait_fn_ensures_fail ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8) -> (y: u8)
                ensures y > 0;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'ensures' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_unwind_fail ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8) -> (y: u8)
                no_unwind;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'unwind' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_unwind_fail_2 ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8) -> (y: u8)
                no_unwind when x > 0;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'unwind' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_mask_fail ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8) -> (y: u8)
                opens_invariants none;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'invariant' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_unsafe_ok ["-V check-api-safety"] => verus_code! {
        pub unsafe trait Foo {
            fn test(x: u8) -> (y: u8)
                ensures y > 0;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] trait_fn_private_ok ["-V check-api-safety"] => verus_code! {
        trait Foo {
            fn test(x: u8) -> (y: u8)
                ensures y > 0;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] trait_fn_impl_requires_fail ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8)
                requires x > 0;
        }

        struct X { }

        impl Foo for X {
            fn test(x: u8) {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_impl_requires_fail_even_if_trait_is_unsafe ["-V check-api-safety"] => verus_code! {
        pub unsafe trait Foo {
            fn test(x: u8)
                requires x > 0;
        }

        struct X { }

        unsafe impl Foo for X {
            fn test(x: u8) {
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] trait_fn_impl_unsafe_ok ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            unsafe fn test(x: u8)
                requires x > 0;
        }

        struct X { }

        impl Foo for X {
            unsafe fn test(x: u8) {
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] trait_fn_impl_with_default_body_and_nontrivial_requires ["-V check-api-safety"] => verus_code! {
        pub trait Foo {
            fn test(x: u8)
                requires x > 0
            {
            }
        }

        struct X { }

        impl Foo for X {
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
}

// There are a few sneaky ways to smuggle private functions to the client
// by using higher-order functions.
// Right now, Verus doesn't support the relevant features; these tests
// will catch these cases in the future.

test_verify_one_file_with_options! {
    #[test] opaque_closure_type_returned ["-V check-api-safety"] => verus_code! {
        pub fn test() -> impl Fn(u32) {
            let f = |y: u32| requires y > 0 { };
            f
        }
    //} => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: opaque type")
}

test_verify_one_file_with_options! {
    #[test] opaque_fndef_type_returned ["-V check-api-safety"] => verus_code! {
        fn test2(y: u32)
            requires y > 0
        {
        }

        pub fn test() -> impl Fn(u32) {
            test2
        }
    //} => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: opaque type")
}

test_verify_one_file_with_options! {
    #[test] fnsig_type_returned ["-V check-api-safety"] => verus_code! {
        fn test2(y: u32)
            requires y > 0
        {
        }

        pub fn test() -> fn(u32) {
            test2
        }
    //} => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'requires' clause is nontrivial")
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: function pointer types")
}
