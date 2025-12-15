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
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not support opaque types together with the check-api-safety flag:")
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
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not support opaque types together with the check-api-safety flag:")
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

test_verify_one_file_with_options! {
    #[test] dyn_returned ["-V check-api-safety"] => verus_code! {
        fn foo(y: u32)
            requires y > 0
        {
        }

        fn test() -> Box<dyn Fn(u32) -> ()> {
            Box::new(foo)
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: dyn")
}

test_verify_one_file_with_options! {
    #[test] any_returned ["-V check-api-safety"] => verus_code! {
        fn foo(y: u32)
            requires y > 0
        {
        }

        fn test() -> Box<dyn core::any::Any> {
            Box::new(foo)
        }
    } => Err(err) => assert_vir_error_msg(err, "trait core::any::Any not declared to Verus")
}

/////// Fancy trait support

test_verify_one_file_with_options! {
    #[test] fancy_0args_fail ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo() -> bool {
                false
            }

            fn exec_fn()
                ensures Self::foo();
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'ensures' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] fancy_0args_ok ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo() -> bool {
                true
            }

            fn exec_fn()
                ensures Self::foo();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_exec_fun_with_body_fail ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                true
            }

            fn exec_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                20
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'ensures' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] fancy_exec_fun_with_body_ok ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                false
            }

            fn exec_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                20
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_exec_fun_without_body_fail ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                true
            }

            fn exec_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'ensures' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] fancy_exec_fun_without_body_ok ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                false
            }

            fn exec_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_with_body_ok ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                false
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                20
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_with_body_ok2 ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                t == 8 && r == 20
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                20
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_with_body_ok3 ["-V check-api-safety"] => verus_code! {
        // The exec version of this fails, but it's okay for proof functions

        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                true
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                20
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_with_body_fail ["-V check-api-safety"] => verus_code! {
        // This fails normally, but if it didn't fail normally, it would need to fail
        // for check-api-safety reasons.

        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                true
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20,
            {
                *t = 8;
                return 21; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_without_body_fail ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                true
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "Safe API violation: 'ensures' clause is nontrivial")
}

test_verify_one_file_with_options! {
    #[test] fancy_proof_fun_without_body_ok ["-V check-api-safety"] => verus_code! {
        pub trait Tr {
            open spec fn foo(t: u64, r: u8) -> bool {
                false
            }

            proof fn proof_fn(t: &mut u64) -> (r: u8)
                ensures Self::foo(*t, r) ==> *t == 8 && r == 20;
        }
    } => Ok(())
}
