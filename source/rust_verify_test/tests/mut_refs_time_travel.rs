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

fn assert_spec_borrowed_field(err: TestErr, var: &str, star: &str, field: &str) {
    assert_rust_error_msg(
        err,
        &format!(
            "cannot borrow `{star}(Verus spec {var}){field}` as immutable because it is also borrowed as mutable"
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
    } => Err(err) => assert_spec_borrowed_field(err, "x_ref", "*", "")
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

test_verify_one_file_with_options! {
    #[test] cant_cheat_prophecy_with_assign_in_has_resolved ["new-mut-ref"] => verus_code! {
        fn test() {
            let ghost nonprophvar: u64 = 0;

            let mut x = 0;
            let x_ref: &mut u64 = &mut x;

            proof {
                let ghost g = has_resolved({ nonprophvar = x; x });
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "assignment is not allowed inside pure context")
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
    } => Err(err) => assert_spec_borrowed_field(err, "a_ref", "*", "")
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
    } => Err(err) => assert_spec_borrowed_field(err, "a_ref", "*", "")
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
    } => Err(err) => assert_spec_borrowed_field(err, "a_ref", "*", "")
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
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".0")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_field ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            assert(x.0 === 0);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".0")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            assert(x.1 === 1);
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut x = (0, 1);
            let x_ref = &mut x.0;
            let ghost g = x.1;
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field_with_deref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.0;
            assert(x.1 === 1);
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field_with_deref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.0;
            let ghost g = x.1;
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_same_field_with_deref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.1;
            assert(x.1 === 1);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".1")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_same_field_with_deref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.1;
            let ghost g = x.1;
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".1")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_same_field_with_explicit_deref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.1;
            assert((*x).1 === 1);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".1")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_same_field_with_explicit_deref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.1;
            let ghost g = (*x).1;
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".1")
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field_with_explicit_deref ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.0;
            assert((*x).1 === 1);
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] borrow_field_and_use_different_field_with_explicit_deref2 ["new-mut-ref"] => verus_code! {
        fn test() {
            let mut y = (0, 1);
            let mut x = &mut y;
            let x_ref = &mut x.0;
            let ghost g = (*x).1;
            *x_ref = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] quant1 ["new-mut-ref"] => verus_code! {
        fn test1() {
            let mut x = 0;
            let x_ref = &mut x;
            let ghost quant = forall|z: u64| z == x;
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] quant2 ["new-mut-ref"] => verus_code! {
        fn test2() {
            let mut x = 0;
            let x_ref = &mut x;
            assert(forall|z: u64| z == x);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] quant3 ["new-mut-ref"] => verus_code! {
        fn test3() {
            let mut x = 0;
            let x_ref = &mut x;
            let ghost quant = ::verus_builtin::forall(|z: u64| z == x);
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] quant4 ["new-mut-ref"] => verus_code! {
        fn test4() {
            let mut x = 0;
            let x_ref = &mut x;
            assert(::verus_builtin::forall(|z: u64| z == x));
            *x_ref = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

// Loop ordering issues

// TODO(new_mut_ref): (blocking) fix the loop issues
test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_decreases_1 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        fn test_loop_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // ok; decreases doesn't need to evaluate at the end
            loop
                decreases a,
            {
                if cond() {
                    z = &mut a;
                    break;
                }

                assume(false);
            }

            *z = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_decreases_2 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        fn test_while_2() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // this should be ok
            while ({
                z = &mut a;
                cond()
            })
                decreases a,
            {
                *z = 20;
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_decreases_3 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        fn test_while_3() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            while ({
                *z = 20;
                cond()
            })
                decreases b, // should fail (comes between `&mut b` and `*z = 20`)
            {
                break;
            }
        }
    } => Err(err) => assert_spec_borrowed(err, "b")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_decreases_4 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn cond() -> bool { true }

        fn test_for_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // should be ok
            for i in 0 .. 10
                decreases a,
            {
                assume(false);
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_ensures_1 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // not ok
            loop
                ensures a == 0 || true,
            {
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_ensures_2 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_2() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // this should be ok
            while ({
                z = &mut a;
                cond()
            })
                ensures a == 0 || true,
            {
                *z = 20;
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_ensures_3 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_3() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // ok
            while ({
                *z = 20;
                cond()
            })
                ensures b == 0 || true,
            {
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_ensures_4 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_for_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // not ok
            for i in 0 .. 10
                ensures a == 0 || true,
            {
                assume(false);
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    //} => Err(err) => assert_spec_borrowed(err, "a")
    } => Err(err) => assert_vir_error_msg(err, "expected curly braces")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_except_break_1 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            assume(false);

            // ok
            loop
                invariant_except_break a == 0 || true,
            {
                if cond() {
                    z = &mut a;
                    break;
                }

                assume(false);
            }

            *z = 20;
        }
    //} => Ok(())
    } => Err(err) => assert_vir_error_msg(err, "expected curly braces")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_except_break_2 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_2() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // this should be ok
            while ({
                z = &mut a;
                cond()
            })
                invariant_except_break a == 0 || true,
            {
                *z = 20;
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_except_break_3 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_3() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // not ok
            while ({
                *z = 20;
                cond()
            })
                invariant_except_break b == 0 || true, // should fail (comes between `&mut b` and `*z = 20`)
            {
                break;
            }
        }
    } => Err(err) => assert_spec_borrowed(err, "b")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_except_break_4 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_for_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // ok
            for i in 0 .. 10
                invariant_except_break a == 0 || true,
            {
                assume(false);
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    } => Err(err) => assert_vir_error_msg(err, "expected curly braces")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_1 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_loop_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // not ok
            loop
                invariant a == 0 || true,
            {
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_2 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_2() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            // this should be ok
            while ({
                z = &mut a;
                cond()
            })
                invariant a == 0 || true,
            {
                *z = 20;
                break;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_3 ["new-mut-ref"] => verus_code! {
        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_while_3() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            while ({
                *z = 20;
                cond()
            })
                invariant b == 0 || true, // should fail (comes between `&mut b` and `*z = 20`)
            {
                break;
            }
        }
    } => Err(err) => assert_spec_borrowed(err, "b")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] test_loop_invariant_4 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn cond() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn test_for_1() {
            let mut a = 0;

            let mut b = 0;
            let mut z = &mut b;

            for i in 0 .. 10
                invariant a == 0 || true,
            {
                assume(false);
                if cond() {
                    z = &mut a;
                    break;
                }
            }

            *z = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "a")
}

test_verify_one_file_with_options! {
    #[test] test_if_let_with_move ["new-mut-ref"] => verus_code! {
        fn consume<A>(a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        fn test_if_let_move(s: Option<X>) {
            if let Option::Some(a) = s {
                let t1 = a;
            } else {
                let t2 = s;
            }
        }

        fn test_if_let_move2(s: Option<(X, X)>) {
            let mut s = s;
            if let Option::Some((a, ref mut b)) = s {
                let t1 = a;
            } else {
                let t2 = s;
            }
        }

        fn test_if_let_move2_in_closure(s: Option<(X, X)>) {
            let clos = || {
                let mut s = s;
                if let Option::Some((a, ref mut b)) = s {
                    let t1 = a;
                } else {
                    let t2 = s;
                }
            };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_if_let_with_move_conjunction ["new-mut-ref", "--edition 2024"] => verus_code! {
        fn consume<A>(a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        fn test_if_let_move_conjunction(s: Option<(X, X)>, cond: bool) {
            // this should be ok, but Verus doesn't support if-let chains right now
            let mut s = s;
            if let Option::Some((a, ref mut b)) = s && cond {
                let t1 = a;
            } else {
                let t2 = s;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "The verifier does not yet support the following Rust feature: let expressions")
}

test_verify_one_file_with_options! {
    #[test] test_if_let_with_move_fail1 ["new-mut-ref", "--no-erasure-check"] => verus_code! {
        fn consume<A>(a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        fn test_if_let_move_fail(s: Option<X>) {
            if let Option::Some(a) = s {
                let t1 = a;
            } else {
                let t2 = s;
                consume(t2);
                consume(t2);
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t2`")
}

test_verify_one_file_with_options! {
    #[test] test_if_let_with_move_fail2 ["new-mut-ref", "--no-erasure-check"] => verus_code! {
        fn consume<A>(a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        fn test_if_let_move2_fail(s: Option<(X, X)>) {
            let mut s = s;
            if let Option::Some((a, ref mut b)) = s {
                let t1 = a;
            } else {
                let t2 = s;
                consume(t2);
                consume(t2);
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t2`")
}

test_verify_one_file_with_options! {
    #[test] test_if_let_with_move_fail3 ["new-mut-ref", "--no-erasure-check"] => verus_code! {
        fn consume<A>(a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        fn test_if_let_move2_fail_in_closure(s: Option<(X, X)>) {
            let clos = || {
                let mut s = s;
                if let Option::Some((a, ref mut b)) = s {
                    let t1 = a;
                } else {
                    let t2 = s;
                    consume(t2);
                    consume(t2);
                }
            };
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t2`")
}

test_verify_one_file_with_options! {
    #[test] proof_mode_test_if_let_with_move ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        proof fn consume<A>(tracked a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        proof fn test_if_let_move(tracked s: Option<X>) {
            if let Option::Some(a) = s {
                let tracked t1 = a;
            } else {
                let tracked t2 = s;
            }
        }

        proof fn test_if_let_move2_in_closure(tracked s: Option<(X, X)>) {
            let tracked clos = proof_fn[Once]|| {
                let tracked mut s = s;
                if let Option::Some(a) = s {
                    let tracked t1 = a;
                } else {
                    let tracked t2 = s;
                }
            };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] proof_mode_test_if_let_with_move_fail ["new-mut-ref"] => verus_code! {
        proof fn consume<A>(tracked a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        proof fn test_if_let_move_fail(tracked s: Option<X>) {
            if let Option::Some(a) = s {
                let tracked t1 = a;
            } else {
                let tracked t2 = s;
                consume(t2);
                consume(t2);
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t2`")
}

test_verify_one_file_with_options! {
    #[test] proof_mode_test_if_let_with_move_fail2 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        proof fn consume<A>(tracked a: A) { }
        struct X { }
        enum Option<V> { Some(V), None }

        proof fn test_if_let_move2_fail_in_closure(tracked s: Option<(X, X)>) {
            let tracked clos = proof_fn[Once]|| {
                let tracked mut s = s;
                if let Option::Some(a) = s {
                    let tracked t1 = a;
                } else {
                    let tracked t2 = s;
                    consume(t2);
                    consume(t2);
                }
            };
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `t2`")
}

test_verify_one_file_with_options! {
    #[test] match_in_loop_invariant_issue2344 ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }

        fn minimal(n: u64) {
            let mut found: Option<u64> = Option::None;
            let mut i: u64 = 0;
            while i < n
                invariant
                    match found { Option::Some(k) => k < 1000u64, Option::None => true }, // FAILS
                decreases n - i,
            {
                found = Option::Some(i);
                i += 1;
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_lifetime_through_closure ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn constrain<T: Fn(&mut (u64, u64)) -> &mut u64>(t: T) -> T
            returns t
        { t }

        fn test1() {
            let c = constrain(|pair: &mut (u64, u64)| -> (fst: &mut u64)
                ensures
                    *fst == old(pair).0,
                    *final(pair) == (*final(fst), old(pair).1),
            {
                &mut pair.0
            });

            let mut pair = (0, 1);
            let r = c(&mut pair);

            assert(pair === (0, 1));

            *r = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "pair")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_whole_shadow_field ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test1() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.b;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x;
            };
            *r = Y { u: 10 };
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `x` because it is borrowed")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_whole ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test1() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.b;
            let clos = move || {
                assert(x == X { a: Y { u: 0 }, b: Y { u: 1 } });
                let x1 = x.a;
            };
            *r = Y { u: 10 };
        }
    } => Err(err) => assert_spec_borrowed(err, "x")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_different_field ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test1() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.b;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x.b;
            };
            *r = Y { u: 10 };
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `x.b` because it is borrowed")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_different_field2 ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test2() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.a;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x.b;
            };
            *r = Y { u: 10 };
        }
    } => Err(err) => assert_spec_borrowed_field(err, "x", "", ".a")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_different_field3 ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y, c: Y }

        fn test2() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 }, c: Y { u: 2 } };
            let r = &mut x.c;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x.b;
            };
            *r = Y { u: 10 };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_same_field ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test1() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.a;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x.a;
            };
            *r = Y { u: 10 };
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot move out of `x.a` because it is borrowed")
}

test_verify_one_file_with_options! {
    #[test] closure_capture_field_shadow_same_field2 ["new-mut-ref"] => verus_code! {
        struct Y { u: u64 }
        struct X { a: Y, b: Y }

        fn test1() {
            let mut x = X { a: Y { u: 0 }, b: Y { u: 1 } };
            let r = &mut x.b;
            let clos = move || {
                assert(x.a == Y { u: 0 });
                let x1 = x.a;
            };
            *r = Y { u: 10 };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] double_closure1 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn test1() {
            let z = 0;
            let clos1 = || {
                let clos2 = || {
                    assert(z == 0);
                };
            };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] double_closure2 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;
        fn test2() {
            let mut z = 0;
            let mut z2 = &mut z;
            let clos1 = || {
                let clos2 = || {
                    assert(z == 0);
                };
            };
            *z2 = 20;
        }
    } => Err(err) => assert_spec_borrowed(err, "z")
}

test_verify_one_file_with_options! {
    #[test] shadow_use_in_pattern_guard ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }

        fn test() {
            let x = Option::Some(3);
            match x {
                Option::Some(y) if ({
                    assert(y == 3);
                    true
                }) => {
                }
                _ => { }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] shadow_use_in_pattern_guard2 ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }

        fn test() {
            let x = Option::Some(3);
            match x {
                Option::Some(y) if ({
                    let j = &mut y;
                    true
                }) => {
                }
                _ => { }
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `y` as mutable, as it is immutable for the pattern guard")
}

test_verify_one_file_with_options! {
    #[test] shadow_use_in_pattern_guard3 ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }

        fn test() {
            let mut z = 20;
            let z_ref = &mut z;
            let x = Option::Some(3);
            match x {
                Option::Some(y) if ({
                    assert(z == 3);
                    true
                }) => {
                }
                _ => { }
            }
            *z_ref = 30;
        }
    } => Err(err) => assert_spec_borrowed(err, "z")
}

test_verify_one_file_with_options! {
    #[test] shadow_use_in_pattern_guard4 ["new-mut-ref"] => verus_code! {
        enum Option<V> { Some(V), None }

        fn test() {
            let x = Option::Some(3);
            match x {
                Option::Some(y) if ({
                    let ghost y1 = y;
                    true
                }) => {
                }
                _ => { }
            }
        }
    } => Ok(())
}
