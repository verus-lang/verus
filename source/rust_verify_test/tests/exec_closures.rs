#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// 1 arg closures

// REVIEW: exec closures implicitly rely on vstd
test_verify_one_file_with_options! {
    #[test] basic_test ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 2
            {
                y
            };

            assert(f.requires((2,)));
            assert(!f.ensures((2,),3));

            let t = f(2);
            assert(t == 2);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3 // FAILS
            {
                y
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail_return_stmt ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3 // FAILS
            {
                return y;
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64|
                requires y == 2
            {
            };

            assert(f.requires((3,))); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_not_ensures_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3
            {
                y + 1
            };

            assert(!f.ensures((2,), 3)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_requires_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64|
                requires y == 2
            {
            };

            f(3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_ensures_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 2
            {
                y
            };

            let z = f(2);
            assert(z == 3); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_loop_forever ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |y: u64|
                requires y == 2
                ensures false
            {
                loop { }
            };

            let z = f(2);
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_requires_is_about_external_var ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn(b: bool) {
            let f = |y: u64|
                requires y == 2
                ensures b
            {
                if !b { loop { } }
            };

            let z = f(2);
            assert(b);
        }
    } => Ok(())
}

// 2 arg closures

test_verify_one_file_with_options! {
    #[test] basic_test_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64| -> (z: u64)
                requires x == y
                ensures z == x
            {
                y
            };

            assert(f.requires((5,5)));
            assert(!f.ensures((2,2),3));

            let t = f(8, 8);
            assert(t == 8);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64| -> (z: u64)
                requires x == y
                ensures z == x // FAILS
            {
                0 as u64
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail_return_stmt_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3 // FAILS
            {
                return 0 as u64;
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64|
                requires y == x
            {
            };

            assert(f.requires((3,4))); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_not_ensures_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64| -> (z: u64)
                requires x == y
                ensures z == x
            {
                y
            };

            assert(!f.ensures((2,2), 2)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_requires_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64|
                requires x == y
            {
            };

            f(3, 4); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_ensures_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let f = |x: u64, y: u64| -> (z: u64)
                requires x == y
                ensures z == x
            {
                y
            };

            let z = f(10, 10);
            assert(z == 11); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// 0 arg closures

test_verify_one_file_with_options! {
    #[test] basic_test_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        // TODO requires/ensures need to be spec-erased
        spec fn goo() -> bool;

        fn testfn() {
            let f = || ensures goo() { assume(goo()); };

            assert(f.requires(()));
            assert(f.ensures((),()) ==> goo());

            let t = f();
            assert(goo());
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                ensures goo() // FAILS
            {
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_ensures_fail_return_stmt_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                ensures goo() // FAILS
            {
                return;
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                requires goo()
            {
            };

            assert(f.requires(())); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_not_ensures_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                ensures goo()
            {
                assume(goo());
            };

            assert(!f.ensures((), ())); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_requires_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                requires goo()
            {
            };

            f(); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_ensures_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        fn testfn() {
            let f = ||
                ensures goo()
            {
                assume(goo());
            };

            let z = f();
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// misc tests

test_verify_one_file_with_options! {
    #[test] pass_closure_via_typ_param ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn f1<T: Fn(u64) -> u64>(t: T)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let ret = t(3);
            assert(ret == 4);
        }

        fn f2() {
            let t = |a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                a + 1
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] pass_closure_via_typ_param_fn_once ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn f1<T: FnOnce(u64) -> u64>(t: T)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let ret = t(3);
            assert(ret == 4);
        }

        fn f2() {
            let t = |a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                a + 1
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] pass_closure_via_typ_param_fn_mut ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn f1<T: FnMut(u64) -> u64>(t: T)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let mut t = t;
            let ret = t(3);
            assert(ret == 4);
        }

        fn f2() {
            let t = |a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                a + 1
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] closure_does_not_support_mut_param_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn() {
            let t = |mut a: u64| { };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support 'mut' params for closures")
}

test_verify_one_file_with_options! {
    #[test] construct_exec_closure_in_spec_code_fail ["vstd"] => (code_str! {
        use vstd::prelude::*;

        // This test needs to be outside the verus macro so that it doesn't
        // automatically add the closure_to_fn_spec wrapper
        #[verifier::spec] fn foo() -> bool {
            let f = || true;
            f()
        }
    }).to_string() => Err(err) => assert_vir_error_msg(err, "closure in ghost code must be marked as a spec_fn")
}

test_verify_one_file_with_options! {
    #[test] call_exec_closure_in_spec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::spec] fn foo<F: Fn(u64) -> u64>(f: F) -> u64 {
            f(5)
        }
    } => Err(err) => assert_vir_error_msg(err, "to call a non-static function in ghost code, it must be a spec_fn")
}

test_verify_one_file_with_options! {
    #[test] construct_fn_spec_in_exec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() {
            let t = closure_to_fn_spec(|x: u64| x);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use spec_fn closure in 'exec' mode")
}

test_verify_one_file_with_options! {
    #[test] call_fn_spec_in_exec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(t: spec_fn(u64) -> u64) {
            let x = t(5);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call spec function from exec mode")
}

test_verify_one_file_with_options! {
    #[test] call_closure_requires_in_exec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() {
            let f = |x: u64| { x };

            let m = call_requires(f, (5, ));
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call spec function from exec mode")
}

test_verify_one_file_with_options! {
    #[test] call_closure_ensures_in_exec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() {
            let f = |x: u64| { x };

            let m = call_ensures(f, (5, ), 7);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call spec function from exec mode")
}

test_verify_one_file_with_options! {
    #[test] ens_type_doesnt_match ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() {
            let f = |x: u64| {
                ensures(|b: bool| b);
                x
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "return type given in `ensures` clause should match")
}

test_verify_one_file_with_options! {
    #[test] mode_check_requires ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn some_exec_fn() -> bool { true }

        fn foo() {
            let f = |x: u64|
                requires some_exec_fn()
            {
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_exec_fn` with mode exec")
}

test_verify_one_file_with_options! {
    #[test] mode_check_ensures ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn some_exec_fn() -> bool { true }

        fn foo() {
            let f = |x: u64|
                ensures some_exec_fn()
            {
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_exec_fn` with mode exec")
}

test_verify_one_file_with_options! {
    #[test] mode_check_return_value ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::spec] fn some_spec_fn() -> bool { true }

        fn foo() {
            let f = |x: u64| {
                some_spec_fn()
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_spec_fn` with mode spec")
}

test_verify_one_file_with_options! {
    #[test] mode_check_return_stmt ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::spec] fn some_spec_fn() -> bool { true }

        fn foo() {
            let f = |x: u64| {
                return some_spec_fn();
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_spec_fn` with mode spec")
}

test_verify_one_file_with_options! {
    #[test] while_loop_inside_closure ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() -> (i: u64)
            ensures i == 0
        {
            let f = || -> (j: u64)
                ensures j == 1
            {
                loop {
                    return 1 as u64;
                }
            };

            assert(false); // FAILS

            0
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_calls_in_assignments_to_mut_var ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(b: bool) {
            let f = |i: u64| -> (j: u64)
                ensures j == i
            {
                i
            };

            let mut r = f(5);

            assert(r == 5);

            if b {
                r = f(7);

                assert(r == 7);
            }

            assert(r == 5 || r == 7);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_calls_in_assignments_to_mut_var_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(b: bool) {
            let f = |i: u64| -> (j: u64)
                ensures j == i
            {
                i
            };

            let mut r = f(5);

            assert(r == 5);

            if b {
                r = f(7);

                assert(r == 7);
            }

            assert(r == 5 || r == 7);
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_calls_as_sub_expression ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn some_call(i: u64)
            requires i == 20
        { }

        fn foo(b: bool) {
            let f = |i: u64| -> (j: u64)
                ensures j == i
            {
                i
            };

            some_call(f(20));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_calls_as_sub_expression_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn some_call(i: u64)
            requires i == 21
        { }

        fn foo(b: bool) {
            let f = |i: u64| -> (j: u64)
                ensures j == i
            {
                i
            };

            some_call(f(20)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] old_works_for_params_from_outside_the_closure ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(b: &mut bool)
            requires *old(b) == true,
        {
            *b = false;

            let f = |i: u64| {
                assert(*b == false);
                assert(*old(b) == true);
            };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] old_for_closure_param_error ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo() {
            let g = |y: u64|
                requires old(y) == 6
            {
                y
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "a mutable reference is expected here")
}

test_verify_one_file_with_options! {
    #[ignore] #[test] callee_is_computed_expression ["vstd"] => verus_code! {
        use vstd::prelude::*;

        // Rust allows this because it can cast both closures to 'fn(u64) -> u64'
        // However Verus doesn't support this type right now

        fn foo(b: bool) {
            let f = |i: u64| { assert(i == 0 || i == 1); i };
            let g = |i: u64| { assert(i == 4 || i == 1); i };
            (if b { f } else { g })(0);
        }

        fn foo2(b: bool) {
            let f = |i: u64| { assert(i == 0 || i == 1); i };
            let g = |i: u64| { assert(i == 4 || i == 1); i };
            (if b { f } else { g })(1); // FAILS
        }

        fn foo3(b: bool) {
            let f = |i: u64| { assert(i == 0 || i == 1); i };
            let g = |i: u64| { assert(i == 4 || i == 1); i };
            (if b { f } else { g })(4); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file_with_options! {
    #[test] callee_is_computed_expression_with_loop ["vstd"] => verus_code! {
        use vstd::prelude::*;

        use vstd::{pervasive::*, prelude::*};

        fn foo(b: bool) {
            let mut i: u64 = 0;

            // This test is written really awkwardly for the sake of getting
            // these two variables, fun1 and fun2, to have the same closure type

            let mut fun1 = Option::None;
            let mut fun2 = Option::None;

            while ({
                // In partictular, we need to do gymnastics to make the closure declaration
                // appear first so that typechecking works.
                // That's why we have all this junk in the condition of the while loop.

                let f = move |j: u64| requires j == 20 || j == i { j };
                if i == 0 { fun1 = Option::Some(f); }
                else if i == 1 { fun2 = Option::Some(f); }

                i = i + 1;

                i < 2
            })
              invariant
                  i == 0 || i == 1 || i == 2,
                  i >= 1 ==> fun1.is_Some() &&
                      (forall|x: u64| (x == 20 || x == 0 ==> fun1.get_Some_0().requires((x,)))),
                  i >= 2 ==> fun2.is_Some() &&
                      (forall|x: u64| (x == 20 || x == 1 ==> fun2.get_Some_0().requires((x,)))),
            {
            }

            assert(i == 2 || i == 3);

            let fun1 = match fun1 { Option::Some(fun1) => fun1, Option::None => unreached() };
            let fun2 = match fun2 { Option::Some(fun1) => fun1, Option::None => unreached() };

            let x = (if b { fun1 } else { fun2 })(20);
        }

        // Same test, but with an assert failure:

        fn foo2(b: bool) {
            let mut i: u64 = 0;

            let mut fun1 = Option::None;
            let mut fun2 = Option::None;

            while ({
                let f = move |j: u64| requires j == 20 || j == i { j };
                if i == 0 { fun1 = Option::Some(f); }
                else if i == 1 { fun2 = Option::Some(f); }

                i = i + 1;

                i < 2
            })
              invariant
                  i == 0 || i == 1 || i == 2,
                  i >= 1 ==> fun1.is_Some() &&
                      (forall|x: u64| (x == 20 || x == 0 ==> fun1.get_Some_0().requires((x,)))),
                  i >= 2 ==> fun2.is_Some() &&
                      (forall|x: u64| (x == 20 || x == 1 ==> fun2.get_Some_0().requires((x,)))),
            {
            }

            assert(i == 2 || i == 3);

            let fun1 = match fun1 { Option::Some(fun1) => fun1, Option::None => unreached() };
            let fun2 = match fun2 { Option::Some(fun1) => fun1, Option::None => unreached() };

            let x = (if b { fun1 } else { fun2 })(0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] name_collisions ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1(b: bool) {
            let x: u64 = 5;
            let f = |x: u64|
                requires x == 6
            {
            };
            f(6);
        }

        fn test2(b: bool) {
            let x: u64 = 5;
            let f = |x: u64|
                requires x == 6
            {
                assert(false); // FAILS
            };
            f(6);
        }

        fn test3(b: bool) {
            let x: u64 = 5;
            let f = |x: u64| -> (x: u64)
                requires x == 6
                ensures x == 7
            {
                7 as u64
            };
            let t = f(6);
            assert(t ==  7);
        }

        fn test4(b: bool) {
            let x: u64 = 7;
            let f = |x: u64| -> (x: u64)
                requires x == 6
                ensures x == 7 // FAILS
            {
                return 8 as u64;
            };
            let t = f(6);
            assert(t ==  7);
        }

        fn test5(b: bool) {
            let x: u64 = 7;
            let f = |x: u64|
                requires x == 6
            {
                let g = |x: u64|
                    requires x == 19
                {
                    assert(false); // FAILS
                };
            };
        }

        fn test6(b: bool) {
            let x: u64 = 7;
            let f = |x: u64|
                requires x == 6
            {
                let g = |x: u64|
                    requires x == 19
                {
                };

                assert(g.requires((19,)));
                assert(g.requires((6,))); // FAILS
            };
        }

        fn test7(b: bool) {
            let x: u64 = 7;
            let f = |x: u64|
                requires x == 6
            {
                assert(x == 6);

                let x = 19;

                assert(x == 19);
                assert(false); // FAILS
            };
        }

        fn test8(b: bool) {
            let x: u64 = 7;
            let f = |x: u64, y: u64|
                requires
                    x == 5 && {
                        let x = y;
                        x != 5
                    }
            {
                assert(x == 5);
                assert(y != 5);
                assert(false); // FAILS
            };
        }

        fn test9(b: bool) {
            let x: u64 = 7;
            let f = |x: u64, y: u64|
                requires
                    x == 5 && {
                        let x = y;
                        x != 5
                    }
            {
            };

            assert(f.requires((5, 7)));
            assert(f.requires((5, 5))); // FAILS
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] return_unit ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let f = |x: u64| -> (res: ())
                ensures res === ()
            {
            };

            let f1 = |x: u64| -> (res: ())
                ensures res === ()
            {
                ()
            };

            let g = |x: u64|
                ensures false
            {
                assume(false);
            };

            assert(g.ensures((2,), ()) ==> false);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] closure_is_dead_end ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let f = |x: u64| {
                assume(false);
            };

            // things proved within the closure should be scoped to within the closure

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] exec_closure_spec_param_error ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let g = |#[verifier::spec] y: u64| {
                5
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "closures only accept exec-mode parameters")
}

test_verify_one_file_with_options! {
    #[test] exec_closure_proof_param_error ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let g = |#[verifier::proof] y: u64| {
                5
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "closures only accept exec-mode parameters")
}

// mut restrictions

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture1 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let mut a = 5;

            let f = |t: u8| {
                a = 7;
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture2 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn takes_mut(u: &mut u64) { }

        fn test1() {
            let mut a = 5;

            let f = |t: u8| {
                takes_mut(&mut a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture3 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn takes_mut(u: &mut u64) { }

        fn test1(a: &mut u64) {
            let f = |t: u8| {
                takes_mut(a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture4 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn takes_mut(u: &mut u64) { }

        fn test1(a: &mut u64) {
            let f = |t: u8| {
                takes_mut(&mut *a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] mut_internal_to_closure_is_okay ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let mut a = 5;

            let f = |t: u8| {
                let mut a = 16;
                a = 7;
            };

            f(7);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture_nested ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let mut a = 5;

            let f = |t: u8| {
                let g = |s: u8| {
                    a = 7;
                };
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture_nested2 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let f = |t: u8| {
                let mut a = 5;
                let g = |s: u8| {
                    a = 7;
                };
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

// closures that depend on type params

test_verify_one_file_with_options! {
    #[test] closure_depends_on_type_param ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test1<T>(some_t: T) {
            let f = |t: T| -> (s: T)
                ensures s == t
            {
                t
            };

            let r = f(some_t);
            assert(equal(r, some_t));
        }
    } => Ok(())
}

// type invariants

test_verify_one_file_with_options! {
    #[test] closure_params_type_invariants_issue457 ["vstd"] => verus_code! {
        fn test(x: u8) {
            assert(x < 256);
            let f = |y: u8| {
                assert(x < 256);
                assert(y < 256);
            };
        }
    } => Ok(())
}

// type well-formed

test_verify_one_file! {
    #[test] error_msg_use_external_type_closure_param verus_code! {
        #[verifier(external)]
        struct X { }

        fn stuff() {
            let f = |x: X| { };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external`")
}

test_verify_one_file! {
    #[test] error_msg_use_external_type_closure_ret verus_code! {
        #[verifier(external)]
        struct X { }

        fn stuff() {
            let f = || -> X { loop { } };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type marked `external`")
}

test_verify_one_file_with_options! {
    #[test] right_decorations_for_tuple_arg ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test<T: Copy, F: std::clone::Clone>(s: &T, key: T, less: F)
            where F: Fn(T, T) -> bool
            requires
                forall |x, y| #[trigger] less.requires((x, y)),
        {
            less(key, *s);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] ref_decoration_in_type_params_issue619 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        // Sometimes when we instantiate a type parameter,
        // either when calling a function, or calling foo.requires or foo.ensures,
        // we end up instantiating it with a reference type &F.
        // This test makes sure we don't have verification failures as a result
        // The ref decoration should be ignored

        fn test0<T: Copy, F>(left: T, right: T, leq: &F)
            where F: Fn(T, T) -> bool
            requires
                forall |x, y| #[trigger] leq.requires((x, y))
        {
            let x = leq(left, right);
        }

        fn moo() {
            let t = || { };
            t();
        }

        fn stuff2<T: FnOnce() -> bool>(t: T)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        fn moo2() {
            let t = || -> (b: bool) ensures b == true { true };
            stuff2(t);
        }

        fn stuff3<T: Fn() -> bool>(t: T)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        fn moo3() {
            let t = || -> (b: bool) ensures b == true { true };
            stuff3(t);
        }

        fn stuff4<T: Fn() -> bool>(t: &T)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        fn moo4() {
            let t = || -> (b: bool) ensures b == true { true };
            stuff4(&t);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] no_impl_fn_once verus_code! {
        struct X { }

        impl FnOnce<(u8, u8)> for X {
            type Output = u8;
            extern "rust-call" fn call_once(self, y: (u8, u8)) -> u8 {
                0
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support implementing this trait")
}

test_verify_one_file! {
    #[test] no_impl_fn_mut verus_code! {
        struct X { }

        #[verifier::external]
        impl FnOnce<(u8, u8)> for X {
            type Output = u8;
            extern "rust-call" fn call_once(self, y: (u8, u8)) -> u8 {
                0
            }
        }

        impl FnMut<(u8, u8)> for X {
            extern "rust-call" fn call_mut(&mut self, y: (u8, u8)) -> u8 {
                0
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support implementing this trait")
}

test_verify_one_file! {
    #[test] no_impl_fn verus_code! {
        struct X { }

        #[verifier::external]
        impl FnOnce<(u8, u8)> for X {
            type Output = u8;
            extern "rust-call" fn call_once(self, y: (u8, u8)) -> u8 {
                0
            }
        }

        #[verifier::external]
        impl FnMut<(u8, u8)> for X {
            extern "rust-call" fn call_mut(&mut self, y: (u8, u8)) -> u8 {
                0
            }
        }

        impl Fn<(u8, u8)> for X {
            extern "rust-call" fn call(&self, y: (u8, u8)) -> u8 {
                0
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support implementing this trait")
}
