#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] old_in_body ["new-mut-ref"] => verus_code! {
        fn test(x: &mut u64)
            requires *x == 0
        {
            *x = 5;

            assert(*x == 5);
            assert(*old(x) == 0);
        }

        fn test_fail(x: &mut u64)
            requires *x == 0
        {
            *x = 5;

            assert(*x == 5);
            assert(*old(x) == 0);
            assert(false); // FAILS
        }

        fn test_field(x: (&mut u64, &mut u64))
            requires *x.0 == 0
        {
            *x.0 = 5;

            assert(*x.0 == 5);
            assert(*old(x.0) == 0);
        }

        fn test_field_fail(x: (&mut u64, &mut u64))
            requires *x.0 == 0
        {
            *x.0 = 5;

            assert(*x.0 == 5);
            assert(*old(x.0) == 0);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] old_in_closure_body ["new-mut-ref"] => verus_code! {
        fn test() {
            let clos = |x: &mut u64|
                requires *x == 0
            {
                *x = 5;
                assert(*x == 5);
                assert(*old(x) == 0);
            };
        }

        fn test_fail() {
            let clos = |x: &mut u64|
                requires *x == 0
            {
                *x = 5;
                assert(*x == 5);
                assert(*old(x) == 0);
                assert(false); // FAILS
            };
        }

        fn test_field() {
            let clos = |x: (&mut u64, &mut u64)|
                requires *x.0 == 0
            {
                *x.0 = 5;
                assert(*x.0 == 5);
                assert(*old(x.0) == 0);
            };
        }

        fn test_field_fail() {
            let clos = |x: (&mut u64, &mut u64)|
                requires *x.0 == 0
            {
                *x.0 = 5;
                assert(*x.0 == 5);
                assert(*old(x.0) == 0);
                assert(false); // FAILS
            };
        }
    } => Err(err) => assert_fails(err, 2)
}

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
    // TODO(new_mut_ref): slightly confusing error msg here
    } => Err(err) => assert_vir_error_msg(err, "`old` for a local variable that isn't a parameter")
}

test_verify_one_file_with_options! {
    #[test] old_of_local ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 24;
            let x_ref = &mut x;
            *x_ref = 30;
            assert(*old(x_ref) == 24);
        }
    } => Err(err) => assert_vir_error_msg(err, "`old` for a local variable that isn't a parameter")
}

test_verify_one_file_with_options! {
    #[test] postcondition_missing_old ["new-mut-ref"] => verus_code! {
        fn test(x: &mut u64)
            ensures *x == 20,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "to dereference a mutable reference parameter in a postcondition, disambiguate by wrapping it either `old` or `final`")
}

test_verify_one_file_with_options! {
    #[test] postcondition_missing_old_closure ["new-mut-ref"] => verus_code! {
        fn test() {
            let clos = |x: &mut u64|
                ensures *x == 20,
            {
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "to dereference a mutable reference parameter in a postcondition, disambiguate by wrapping it either `old` or `final`")
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
    #[test] postcondition_missing_old_for_tuple ["new-mut-ref"] => verus_code! {
        fn test(x: (&mut u64, &mut u64))
            ensures *x.1 == 20,
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "to dereference a mutable reference parameter in a postcondition, disambiguate by wrapping it either `old` or `final`")
}

test_verify_one_file_with_options! {
    #[test] postcondition_old_fin_tuple_ok ["new-mut-ref"] => verus_code! {
        fn test(x: (&mut u64, &mut u64))
            requires *x.1 < 10,
            ensures *fin(x.1) == *old(x.1) + 1
        {
            *x.1 = *x.1 + 1;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] postcondition_old_fin_tuple_ok_2 ["new-mut-ref"] => verus_code! {
        // I intend for this to also be ok but `old` is currently restricted to &mut -> &mut
        fn test2(x: (&mut u64, &mut u64))
            requires *x.1 < 10,
            ensures *fin(x.1) == *old(x).1 + 1
        {
            *x.1 = *x.1 + 1;
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file_with_options! {
    #[test] old_containing_fin ["new-mut-ref"] => verus_code! {
        fn test2(x: &mut u64)
            ensures *old(fin(x)) == 20
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "The result of `fin` must be dereferenced")
}

test_verify_one_file_with_options! {
    #[test] fin_containing_old ["new-mut-ref"] => verus_code! {
        // bizarre thing to write, but there's no reason to disallow it
        fn test2(x: &mut u64)
            ensures *fin(old(x)) == 20
        {
            *x = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] nested_mut_refs ["new-mut-ref"] => verus_code! {
        #[verifier::exec_allows_no_decreases_clause]
        fn leak_mut_ref() -> (res: &'static mut u64)
            ensures
                *res == 2,
                *fin(res) == 19, // It's obviously impossible to predict this
        {
            loop { }
        }

        fn test0(x: &mut &mut u64)
            requires
                *old(*old(x)) == 0,
            ensures
                mut_ref_current(mut_ref_current(x)) == 0,
                mut_ref_future(mut_ref_current(x)) == 1,
                mut_ref_current(mut_ref_future(x)) == 3,
                mut_ref_future(mut_ref_future(x)) == 19,
        {
            **x = 1;
            *x = leak_mut_ref();
            **x = 3;
        }

        fn test1(x: &mut &mut u64)
            requires
                *old(*old(x)) == 0,
            ensures
                *old(*old(x)) == 0,
                *fin(*old(x)) == 1,
                *old(*fin(x)) == 3,
                *fin(*fin(x)) == 19,
        {
            **x = 1;
            *x = leak_mut_ref();
            **x = 3;
        }

        // old isn't needed for the outer derefs
        fn test2(x: &mut &mut u64)
            requires
                *old(*old(x)) == 0,
            ensures
                **old(x) == 0,
                *fin(*old(x)) == 1,
                **fin(x) == 3,
                *fin(*fin(x)) == 19,
        {
            **x = 1;
            *x = leak_mut_ref();
            **x = 3;
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

test_verify_one_file_with_options! {
    // TODO(new_mut_ref): currently malformed AIR error
    #[ignore] #[test] test_assert_nonlinear ["new-mut-ref"] => verus_code! {
        fn nonlinear(x: &mut u64)
            requires *x == 0,
        {
            *x = 5;
            assert(*x == 0 && *old(x) == 5) by(nonlinear_arith);
        }

        fn nonlinear2(x: &mut u64) {
            assert(*x == 0 && *old(x) == 5) by(nonlinear_arith)
              requires *x == 0 && *old(x) == 5;
        }
    } => Err(err) => assert_vir_error_msg(err, "old not allowed in assert-by-nonlinear")
}

test_verify_one_file_with_options! {
    // TODO(new_mut_ref): currently malformed AIR error
    #[ignore] #[test] test_assert_bv ["new-mut-ref"] => verus_code! {
        fn nonlinear(x: &mut u64)
            requires *x == 0,
        {
            *x = 5;
            assert(*x == 0 && *old(x) == 5) by(bit_vector);
        }

        fn nonlinear2(x: &mut u64) {
            assert(*x == 0 && *old(x) == 5) by(bit_vector)
              requires *x == 0 && *old(x) == 5;
        }
    } => Err(err) => assert_vir_error_msg(err, "old not allowed in assert-by-bitvector")
}

test_verify_one_file_with_options! {
    // TODO(new_mut_ref): some issue with the closure being interpreted as taking a mutable borrow
    #[ignore] #[test] old_in_closure_referring_to_outer_param ["new-mut-ref"] => verus_code! {
        fn test(x: &mut u64)
            requires *x == 0,
        {
            *x = 5;

            let mut clos = ||
                requires *old(x) == 0
            {
                assert(*old(x) == 0);
            };

            assert(*old(x) == 0);
            clos();
        }

        fn test2(x: &mut u64)
            requires *x == 0,
        {
            *x = 5;

            let mut clos = ||
                requires *x == 5
            {
                assert(*x == 5);
            };

            clos();
        }

        fn test3(x: &mut u64)
            requires *x == 0,
        {
            let mut clos = ||
                requires *x == 5
            {
                assert(*x == 5);
            };

            *x = 5;

            clos(); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] unwrap_params ["new-mut-ref"] => verus_code! {
        fn test(Tracked(x): Tracked<&mut Ghost<int>>)
            requires *x == 0,
            ensures fin(x)@ == old(x)@ + 3,
        {
            proof {
                *x = Ghost(3);
            }

            assert(*x == 3);
            assert(*old(x) == 0);
        }

        fn test_fail(Tracked(x): Tracked<&mut Ghost<int>>)
            requires *x == 0,
        {
            proof {
                *x = Ghost(3);
            }

            assert(*x == 3);
            assert(*old(x) == 0);
            assert(false); // FAILS
        }

        fn caller() {
            let mut x: Ghost<int> = Ghost(0);
            test(Tracked(&mut x));
            assert(x == 3);
        }

        fn caller_fail() {
            let mut x: Ghost<int> = Ghost(0);
            test(Tracked(&mut x));
            assert(x == 3);
            assert(false); // FAILS
        }

        fn caller_fail2() {
            let mut x: Ghost<int> = Ghost(1);
            test(Tracked(&mut x)); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
