#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] old_in_spec_fn ["new-mut-ref"] => verus_code! {
        spec fn foo(x: &mut u64) -> u64 {
            *old(x)
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless in spec functions")
}

test_verify_one_file_with_options! {
    #[test] old_in_spec_fn_sig ["new-mut-ref"] => verus_code! {
        spec fn foo(x: &mut u64) -> u64
            recommends *old(x) == 0
        {
            0
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless in spec functions")
}

test_verify_one_file_with_options! {
    #[test] old_of_spec_closure_param ["new-mut-ref"] => verus_code! {
        proof fn test() {
            let x = |a: &mut u64| *old(a) == 0;
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` is meaningless for parameter of spec closure")
}

test_verify_one_file_with_options! {
    #[test] old_of_local ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 24;
            x = 30;
            assert(*old(x) == 24);
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` does not apply to locals")
}

test_verify_one_file_with_options! {
    #[test] postcondition_missing_old ["new-mut-ref"] => verus_code! {
        fn test(x: &mut u64)
            ensures *x == 20,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "missing old or final")
}

test_verify_one_file_with_options! {
    #[test] postcondition_missing_old_for_return_is_ok ["new-mut-ref"] => verus_code! {
        fn test(x: &mut u64) -> (y: &mut u64)
            ensures *y == *old(x) && *fin(y) == *fin(x),
        {
            x
        }
    } => Ok(())
}



        

test_verify_one_file_with_options! {
    #[test] test_assert_by ["new-mut-ref"] => verus_code! {
        fn test1_assert_by(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert(*old(x) == 1) by { }; // FAILS
        }

        fn test2_assert_by(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert(*x == 0) by { }; // FAILS
        }

        fn test3_assert_by(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert(*old(x) == 0 && *x == 1) by { };
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] test_assert_forall ["new-mut-ref"] => verus_code! {
        spec fn foo(z: bool) -> bool { z }

        fn test1_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| #[trigger] foo(z) implies *old(x) == 1 by { }; // FAILS
        }

        fn test2_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| #[trigger] foo(z) implies *x == 0 by { }; // FAILS
        }

        fn test3_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| #[trigger] foo(z) implies *old(x) == 0 && *x == 1 by { };
            assert(!foo(false));
            assert(foo(true));
            assert(false); // FAILS
        }

        fn test4_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| *old(x) != 1 implies #[trigger] foo(z) by { }; // FAILS
        }

        fn test5_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| *x != 0 implies #[trigger] foo(z) by { }; // FAILS
        }

        fn test6_assert_forall(x: &mut u64)
            requires *x == 0,
        {
            *x = 1;
            assert forall |z| !(*old(x) == 0 && *x == 1) implies #[trigger] foo(z) by { };
            assert(!foo(false));
            assert(foo(true));
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

