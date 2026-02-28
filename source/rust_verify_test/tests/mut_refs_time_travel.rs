#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn assert_spec_borrowed(err: TestErr, var: &str) {
    assert_rust_error_msg(
        err,
        &format!(
            "cannot borrow `(Verus spec {var})` as immutable because it is also borrowed as mutable"
        ),
    )
}

test_verify_one_file_with_options! {
    #[test] test_basic_fails ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;
            assert(x == 0);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] test_basic_reborrow_fails ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;
            let x_ref2 = &mut *x_ref;
            assert(*x_ref == 0);
            *x_ref2 = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x_ref")
}

test_verify_one_file_with_options! {
    #[test] test_basic_fails_let_ghost ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let x_ref = &mut x;
            let ghost y = x;
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] test_ref_mut_binding_fails ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = 0;
            let ref mut x_ref = x;
            assert(x == 0);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] test_ok_with_after_borrow ["new-mut-ref"] => verus_code! {
        fn test_after_borrow() {
            let mut x = 0;
            let ref mut x_ref = x;
            assert(after_borrow(x) == after_borrow(x));
            *x_ref = 20;
        }

        fn test_after_borrow2() {
            let mut x = 0;
            let ref mut x_ref = x;
            assert(after_borrow(x) == 0); // FAILS
            *x_ref = 20;
        }

        fn test_after_borrow3() {
            let mut x = 0;
            let ref mut x_ref = x;
            let ghost proph = after_borrow(x);
            *x_ref = 20;
            assert(proph == 20);
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] test_ok_with_has_resolved ["new-mut-ref"] => verus_code! {
        fn test_after_borrow() {
            let mut x = 0;
            let ref mut x_ref = x;
            assert(has_resolved(x));
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] cant_cheat_prophecy_with_assign_in_after_borrow ["new-mut-ref"] => verus_code! {
        fn test() {
            let ghost nonprophvar: u64 = 0;

            let mut x = 0;
            let x_ref: &mut u64 = &mut x;

            proof {
                let ghost g = after_borrow({ nonprophvar = x; x });
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "`after_borrow` expects a local variable, possibly with dereferences or field accesses")
}

// TODO(new_mut_ref): fix this
test_verify_one_file_with_options! {
    #[ignore] #[test] cant_cheat_prophecy_with_assign_in_has_resolved ["new-mut-ref"] => verus_code! {
        fn test() {
            let ghost nonprophvar: u64 = 0;

            let mut x = 0;
            let x_ref: &mut u64 = &mut x;

            proof {
                let ghost g = has_resolved({ nonprophvar = x; x });
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed")
}

test_verify_one_file_with_options! {
    #[test] test_borrow_and_pattern_match ["new-mut-ref"] => verus_code! {
        fn test2() {
            let mut x = (0, 1);
            let (x_ref, _) = &mut x;
            assert(x === (0, 1));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] test_borrow_and_pattern_match2 ["new-mut-ref"] => verus_code! {
        fn test3() {
            let mut x = (0, 1);
            let z = &mut x;
            let (x_ref, _) = z;
            assert(x === (0, 1));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] test_let_else ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }
        fn test4() {
            let mut x = Option::Some(0);
            let z = &mut x;
            let Option::Some(x_ref) = z else { loop{} };
            assert(x === Option::Some(0));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] ref_mut_binding_in_match ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }
        fn test5() {
            let mut x = Option::Some(0);
            match x {
                Option::Some(ref mut x_ref) => {
                    assert(x === Option::Some(0));
                    *x_ref = 20;
                }
                Option::None => { }
            }
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] ref_mut_binding_in_if_let ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }
        fn test_let_expr() {
            let mut o = Option::Some(0);
            if let Option::Some(ref mut x_ref) = o {
                assert(o === Option::Some(0));
                *x_ref = 20;
            }
        }
    } => Err(err) => assert_spec_borrowed(err, "o")
}

test_verify_one_file_with_options! {
    #[test] ref_mut_binding_in_pat_let_decl ["new-mut-ref"] => verus_code! {
        fn test13() {
            let mut x = (0, 1);
            let (ref mut x_ref, l) = x;
            assert(x === (0, 1));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] two_phase1 ["new-mut-ref"] => verus_code! {
        fn check<'a>(a: &'a mut u64, b: &'a mut u64) -> &'a u64 { &*a }

        fn twophase1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;

            let c = check(a_ref, b_ref);

            assert(a == 0);

            let x = *c;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[test] two_phase2 ["new-mut-ref"] => verus_code! {
        fn check<'a>(a: &'a mut u64, b: &'a mut u64) -> (res: &'a u64) { &*a }

        fn twophase2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;

            let c = check(a_ref, b_ref);

            assert(*a_ref == 0);

            let x = *c;
        }
    } => Err(err) => assert_spec_borrowed(err, "a_ref")
}

test_verify_one_file_with_options! {
    #[test] two_phase3 ["new-mut-ref"] => verus_code! {
        fn check<'a>(a: &'a mut u64, b: &'a mut u64) -> (res: &'a mut u64) { &mut *a }

        fn twophase2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;

            let c = check(a_ref, b_ref);

            assert(*a_ref == 0);

            *c = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "a_ref")
}

test_verify_one_file_with_options! {
    #[test] two_phase4 ["new-mut-ref"] => verus_code! {
        fn check<T>(a: T, b: T) -> (res: T) { a }

        fn twophase2() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;

            // generic means there's no reborrow
            let c = check(a_ref, b_ref);

            // so *a_ref hasn't been borrowed from; so this is ok
            assert(*a_ref == 0);

            *c = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] two_phase5 ["new-mut-ref"] => verus_code! {
        fn check<'a>(a: &'a mut u64, b: &'a mut u64) -> &'a u64 { &*a }

        fn twophase1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;

            let c = check(a_ref, ({
                assert(*a_ref == 0);
                b_ref
            }));

            let x = *c;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] param ["new-mut-ref"] => verus_code! {
        fn param_failure(mut x: u64) {
            let y = &mut x;
            assert(x == 0);
            *y = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] param_old_use_ok ["new-mut-ref"] => verus_code! {
        fn param_ok(mut x: &mut u64)
            requires *x == 0,
        {
            let y = &mut x;
            assert(*old(x) == 0);
            **y = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] closure_local ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let clos = || {
                let mut x = 0;
                let y = &mut x;
                assert(x == 0);
                *y = 20;
            };
            clos();
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] closure_param ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let clos = |mut x: u64, z: &mut u64| {
                let y = &mut x;
                assert(x == 0);
                *y = 20;
            };
            let mut z = 0;
            let z_ref = &mut z;
            clos(0, z_ref);
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] double_closure_param ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let clos2 = || {
                let clos = |mut x: u64, z: &mut u64| {
                    let y = &mut x;
                    assert(x == 0);
                    *y = 20;
                };
                let mut z = 0;
                let z_ref = &mut z;
                clos(0, z_ref);
            };
            clos2();
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] closure_capture ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;

            let clos = |x: u64| {
                assert(y == 0);
            };

            *y_ref = 20;

            clos(0);
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_let_ghost ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;

            let clos = |x: u64| {
                let ghost j = y;
            };

            *y_ref = 20;

            clos(0);
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_in_requires ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;

            let clos = |x: u64|
                requires y == 0
            {
            };

            *y_ref = 20;

            clos(0);
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_in_ensures ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;

            let clos = |x: u64|
                ensures y == 0
            {
            };

            *y_ref = 20;

            clos(0);
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] misc_borrows_and_reborrows ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;   // call this lifetime 'a

            let a_ref2 = a_ref;

            a_ref = &mut b;
            assert(*a_ref == 0);      // this is okay because a_ref no longer depends on 'a

            *a_ref2 = 20;             // lifetime 'a last to here
        }

        fn test2() {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;

            let a_ref2 = a_ref;

            a_ref = &mut b;

            assert(a == 0);

            let r = &mut *a_ref;
        }

        fn test3() {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;

            let a_ref2 = a_ref;

            a_ref = &mut b;

            assert(*a_ref == 0);
        }

        fn test4() {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;

            let a_ref2 = a_ref;

            a_ref = &mut b;

            assert(*a_ref == 0);
        }

        fn test5() {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;
            a_ref = &mut b;

            let z = &mut a;

            let w = &mut *a_ref;
        }

        // These require processing of assignments:

        fn test6(cond: bool) {
            let mut a = 0;
            let mut b = 0;

            let mut a_ref = &mut a;

            a_ref = &mut *a_ref;
            a_ref = &mut *a_ref;
        }

        fn test7(cond: bool) {
            let mut a = 0;
            let mut b = 0;

            let mut x_ref = &mut a;

            let mut reborrow = &mut *x_ref;
            x_ref = &mut b;
            let mut reborrow2 = &mut *x_ref;

            *reborrow = 20;
            *reborrow2 = 30;

            assert(a == 20);
            assert(b == 30);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] generic_instantiation ["new-mut-ref", "--no-erasure-check"] => verus_code! {
        fn f<T>(a: T) -> T { a }
        fn test<'a>(a: &'a mut u64, b: u64) -> &'a mut u64 { a }

        fn generic_instantiation() {
            let mut a = 0;
            let mut b = 0;
            let mut a_ref = &mut a;
            let mut b_ref = &mut b;
            let a_ref2 = test(f(a_ref), *a_ref);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot use `*a_ref` because it was mutably borrowed")
}

test_verify_one_file_with_options! {
    #[test] generic_instantiation2 ["new-mut-ref"] => verus_code! {
        fn f<T>(a: T) -> T { a }
        fn test<'a>(a: &'a mut u64, b: u64) -> &'a mut u64 { a }

        fn generic_instantiation2() {
            let mut a = 0;
            let mut b = 0;
            let mut a_ref = &mut a;
            let mut b_ref = &mut b;
            let a_ref2 = test(f(a_ref), ({ assert(*a_ref == 0); 0 }));
        }
    } => Err(err) => assert_spec_borrowed(err, "a_ref")
}

test_verify_one_file_with_options! {
    #[test] generic_instantiation3 ["new-mut-ref"] => verus_code! {
        fn f<T>(a: T) -> T { a }
        fn test<'a>(a: &'a mut u64, b: u64) -> &'a mut u64 { a }

        fn generic_instantiation2() {
            let mut a = 0;
            let mut b = 0;
            let mut a_ref = &mut a;
            let mut b_ref = &mut b;
            let a_ref2 = test(f(a_ref), 0);
            assert(a == 0);
            *a_ref2 = 0;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[test] spec_closure_use ["new-mut-ref"] => verus_code! {
        spec fn foo(t: u64, y: u64) -> bool { true }

        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;
            let ghost z = |t: u64| foo(t, y);
            *y_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] assert_forall_use ["new-mut-ref"] => verus_code! {
        spec fn foo(t: u64, y: u64) -> bool { true }

        fn closure_test() {
            let mut y = 0;
            let y_ref = &mut y;
            assert forall |t: u64| t > 0 implies foo(t, y) by { }
            *y_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "y")
}

test_verify_one_file_with_options! {
    #[test] two_phase_closure_call ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn constrain<F>(f: F) -> F
        where
            F: for<'a> Fn(&'a mut u64, &'a mut u64) -> &'a mut u64
        {
            f
        }

        fn twophase1() {
            let mut a: u64 = 0;
            let mut b: u64 = 0;
            let a_ref = &mut a;
            let b_ref = &mut b;
            let check = constrain(|a: &mut u64, b: &mut u64| { a });

            let c = check(a_ref, b_ref);

            assert(a == 0);
            let x = *c;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_whole ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            assert(x === (0, 1));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] borrow_whole_and_use_field ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x;
            assert(x.0 === 0);
            *x_ref = (20, 21);
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_field ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            assert(x.0 === 0);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

// TODO(new_mut_ref): fix
test_verify_one_file_with_options! {
    #[ignore] #[test] borrow_field_and_use_different_field ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            assert(x.1 === 1);
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] borrow_field_and_use_different_field2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            let ghost g = x.1;
            *x_ref = 20;
        }
    } => Ok(())
}
