#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/////////////////////////////////////////////////////
// Begin:
// These tests were adapted from exec_closures.rs
// ------------------------------------------------->

// 1 arg closures

// REVIEW: proof closures, like exec closures, implicitly rely on vstd
test_verify_one_file_with_options! {
    #[test] basic_test ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked f = proof_fn|y: u64| -> (z: u64)
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

        proof fn testfn() {
            let tracked f = proof_fn|y: u64| -> (z: u64)
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

        proof fn testfn() {
            let tracked f = proof_fn|y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3 // FAILS
            {
                return y;
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support `return` inside `proof_fn`")
    // TODO: } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked f = proof_fn|y: u64|
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

        proof fn testfn() {
            let tracked f = proof_fn|y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3
            {
                (y + 1) as u64
            };

            assert(!f.ensures((2,), 3)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_call_requires_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked f = proof_fn|y: u64|
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

        proof fn testfn() {
            let tracked f = proof_fn|y: u64| -> (z: u64)
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
            let tracked f = proof_fn|y: u64|
                requires y == 2
                ensures false
            {
                loop { }
            };

            let z = f(2);
            assert(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof")
}

test_verify_one_file_with_options! {
    #[test] test_requires_is_about_external_var ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn(b: bool) {
            let tracked f = proof_fn|y: u64|
                requires y == 2
                ensures b
            {
                if !b { loop { } }
            };

            let z = f(2);
            assert(b);
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof")
}

// 2 arg closures

test_verify_one_file_with_options! {
    #[test] basic_test_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64| -> (z: u64)
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

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64| -> (z: u64)
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

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64| -> (z: u64)
                requires y == 2
                ensures z == 3 // FAILS
            {
                return 0 as u64;
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support `return` inside `proof_fn`")
    //TODO } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail_2_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64|
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

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64| -> (z: u64)
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

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64|
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

        proof fn testfn() {
            let tracked f = proof_fn|x: u64, y: u64| -> (z: u64)
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
        uninterp spec fn goo() -> bool;

        proof fn testfn() {
            let tracked f = proof_fn|| ensures goo() { assume(goo()); };

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

        proof fn testfn() {
            let tracked f = proof_fn||
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

        proof fn testfn() {
            let tracked f = proof_fn||
                ensures goo() // FAILS
            {
                return;
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support `return` inside `proof_fn`")
    //TODO } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test_assert_requires_fail_0_args ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn goo() -> bool;

        proof fn testfn() {
            let tracked f = proof_fn||
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

        proof fn testfn() {
            let tracked f = proof_fn||
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

        proof fn testfn() {
            let tracked f = proof_fn||
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

        proof fn testfn() {
            let tracked f = proof_fn||
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

        proof fn f1<T: ProofFn>(tracked t: proof_fn<T>(u64) -> u64)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let ret = t(3);
            assert(ret == 4);
        }

        proof fn f2() {
            let tracked t = proof_fn|a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                (a + 1) as u64
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] pass_closure_via_typ_param_fn_once ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn f1<T: ProofFnOnce>(tracked t: proof_fn<T>(u64) -> u64)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let ret = t(3);
            assert(ret == 4);
        }

        proof fn f2() {
            let tracked t = proof_fn|a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                (a + 1) as u64
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] pass_closure_via_typ_param_fn_mut ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn f1<T: ProofFnMut>(tracked t: proof_fn<T>(u64) -> u64)
            requires
                forall|x: u64| 0 <= x < 5 ==> t.requires((x,)),
                forall|x: u64, y: u64| t.ensures((x,), y) ==> y == x + 1,
        {
            let tracked mut t = t;
            let ret = t(3);
            assert(ret == 4);
        }

        proof fn f2() {
            let tracked t = proof_fn|a: u64| -> (ret: u64)
                requires 0 <= a < 5
                ensures ret == a + 1
            {
                (a + 1) as u64
            };

            f1(t);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] closure_does_not_support_mut_param_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn testfn() {
            let tracked t = proof_fn|mut a: u64| { };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support 'mut' params for closures")
}

test_verify_one_file_with_options! {
    #[test] construct_exec_closure_in_spec_code_fail ["vstd"] => (code_str! {
        use vstd::prelude::*;

        verus! {
            type t = proof_fn<'static>() -> bool;
        }
        // This test needs to be outside the verus macro so that it doesn't
        // automatically add the closure_to_fn_spec wrapper
        #[verifier::spec] fn foo() -> bool {
            let f: t = closure_to_fn_proof(|| true);
            f()
        }
    }).to_string() => Err(err) => assert_vir_error_msg(err, "proof closure can only appear in proof mode")
}

test_verify_one_file_with_options! {
    #[test] call_exec_closure_in_spec_code_fail ["vstd"] => verus_code! {
        use vstd::prelude::*;

        spec fn foo(f: proof_fn(u64) -> u64) -> u64 {
            f(5)
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function with mode proof")
}

// Omitting construct_fn_spec_in_exec_code_fail; it is irrelevant to proof mode
// Omitting call_fn_spec_in_exec_code_fail; it is irrelevant to proof mode
// Omitting call_closure_requires_in_exec_code_fail; it is irrelevant to proof mode
// Omitting call_closure_ensures_in_exec_code_fail; it is irrelevant to proof mode

test_verify_one_file_with_options! {
    #[test] ens_type_doesnt_match ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo() {
            let tracked f = proof_fn|x: u64| {
                ensures(|b: bool| b);
                x
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "return type given in `ensures` clause should match")
}

test_verify_one_file_with_options! {
    #[test] mode_check_requires ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn some_proof_fn() -> bool { true }

        proof fn foo() {
            let tracked f = proof_fn|x: u64|
                requires some_proof_fn()
            {
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function `test_crate::some_proof_fn` with mode proof")
}

test_verify_one_file_with_options! {
    #[test] mode_check_ensures ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn some_exec_fn() -> bool { true }

        proof fn foo() {
            let tracked f = proof_fn|x: u64|
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

        proof fn foo() {
            let tracked f = proof_fn|x: u64| -> tracked bool {
                some_spec_fn()
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] mode_check_return_stmt ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::spec] fn some_spec_fn() -> bool { true }

        proof fn foo() {
            let tracked f = proof_fn|x: u64| -> tracked bool {
                return some_spec_fn();
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support `return` inside `proof_fn`")
    //TODO } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] loop_inside_closure ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo() -> (i: u64)
            ensures i == 0
        {
            let tracked f = proof_fn|| -> (j: u64)
                ensures j == 1
            {
                loop {
                }
            };

            assert(false); // FAILS

            0
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use while in proof")
}

test_verify_one_file_with_options! {
    #[test] test_calls_in_assignments_to_mut_var ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo(b: bool) {
            let tracked f = proof_fn|i: u64| -> (j: u64)
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

        proof fn foo(b: bool) {
            let tracked f = proof_fn|i: u64| -> (j: u64)
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

        proof fn some_call(i: u64)
            requires i == 20
        { }

        proof fn foo(b: bool) {
            let tracked f = proof_fn|i: u64| -> (j: u64)
                ensures j == i
            {
                i
            };

            // Note: since the parameter i is a spec-mode parameter,
            // the argument must be a pure spec-mode expression,
            // and pure spec-mode expressions cannot contain exec or proof calls,
            // so the following is an error:
            some_call(f(20));
            // By contrast, "let x = f(20); some_call(x)" succeeds.
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call function with mode proof")
}

// Omitting test_calls_as_sub_expression_fail; it is the same as test_calls_as_sub_expression

test_verify_one_file_with_options! {
    #[test] old_works_for_params_from_outside_the_closure ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo(b: &mut bool)
            requires *old(b) == true,
        {
            *b = false;

            let tracked f = proof_fn|i: u64| {
                assert(*b == false);
                assert(*old(b) == true);
            };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] old_for_closure_param_error ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo() {
            let tracked g = proof_fn|y: u64|
                requires old(y) == 6
            {
                y
            };
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file_with_options! {
    #[test] callee_is_computed_expression ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn foo(b: bool) {
            let tracked f = proof_fn|i: u64| requires i == 0 || i == 1 { i };
            let tracked g = proof_fn|i: u64| requires i == 4 || i == 1 { i };
            (if b { f } else { g })(1);
        }

        proof fn foo2(b: bool) {
            let tracked f = proof_fn|i: u64| requires i == 0 || i == 1 { i };
            let tracked g = proof_fn|i: u64| requires i == 4 || i == 1 { i };
            (if b { f } else { g })(0); // FAILS
        }

        proof fn foo3(b: bool) {
            let tracked f = proof_fn|i: u64| requires i == 0 || i == 1 { i };
            let tracked g = proof_fn|i: u64| requires i == 4 || i == 1 { i };
            (if b { f } else { g })(4); // FAILS
        }
    } => Err(e) => assert_fails(e, 2)
}

// Omitting callee_is_computed_expression_with_loop since proofs don't support loops

test_verify_one_file_with_options! {
    #[test] name_collisions ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn test1(b: bool) {
            let x: u64 = 5;
            let tracked f = proof_fn|x: u64|
                requires x == 6
            {
            };
            f(6);
        }

        proof fn test2(b: bool) {
            let x: u64 = 5;
            let tracked f = proof_fn|x: u64|
                requires x == 6
            {
                assert(false); // FAILS
            };
            f(6);
        }

        proof fn test3(b: bool) {
            let x: u64 = 5;
            let tracked f = proof_fn|x: u64| -> (x: u64)
                requires x == 6
                ensures x == 7
            {
                7 as u64
            };
            let t = f(6);
            assert(t ==  7);
        }

        proof fn test4(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64| -> (x: u64)
                requires x == 6
                ensures x == 7 // FAILS
            {
                8 as u64
            };
            let t = f(6);
            assert(t ==  7);
        }

        proof fn test5(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64|
                requires x == 6
            {
                let tracked g = proof_fn|x: u64|
                    requires x == 19
                {
                    assert(false); // FAILS
                };
            };
        }

        proof fn test6(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64|
                requires x == 6
            {
                let tracked g = proof_fn|x: u64|
                    requires x == 19
                {
                };

                assert(g.requires((19,)));
                assert(g.requires((6,))); // FAILS
            };
        }

        proof fn test7(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64|
                requires x == 6
            {
                assert(x == 6);

                let x: int = 19;

                assert(x == 19);
                assert(false); // FAILS
            };
        }

        proof fn test8(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64, y: u64|
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

        proof fn test9(b: bool) {
            let x: u64 = 7;
            let tracked f = proof_fn|x: u64, y: u64|
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

        proof fn test() {
            let tracked f = proof_fn|x: u64| -> (res: ())
                ensures res === ()
            {
            };

            let tracked f1 = proof_fn|x: u64| -> (res: ())
                ensures res === ()
            {
                ()
            };

            let tracked g = proof_fn|x: u64|
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

        proof fn test() {
            let tracked f = proof_fn|x: u64| {
                assume(false);
            };

            // things proved within the closure should be scoped to within the closure

            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Omitting exec_closure_spec_param_error because proof function accept spec parameters
// Omitting exec_closure_proof_param_error because proof function accept tracked parameters

// mut restrictions

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture1 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn test1() {
            let mut a: int = 5;

            let tracked f = proof_fn|t: u8| {
                a = 7;
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture2 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn takes_mut(u: &mut u64) { }

        proof fn test1() {
            let mut a = 5;

            let tracked f = proof_fn|t: u8| {
                takes_mut(&mut a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture3 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn takes_mut(u: &mut u64) { }

        proof fn test1(a: &mut u64) {
            let tracked f = proof_fn|t: u8| {
                takes_mut(a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture4 ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn takes_mut(u: &mut u64) { }

        proof fn test1(a: &mut u64) {
            let tracked f = proof_fn|t: u8| {
                takes_mut(&mut *a);
            };

            f(7);
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support closures capturing a mutable reference")
}

test_verify_one_file_with_options! {
    #[test] mut_internal_to_closure_is_okay ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn test1() {
            let mut a: int = 5;

            let tracked f = proof_fn|t: u8| {
                let mut a: int = 16;
                a = 7;
            };

            f(7);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] disallowed_mut_capture_nested ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn test1() {
            let mut a: int = 5;

            let tracked f = proof_fn|t: u8| {
                let tracked g = proof_fn|s: u8| {
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

        proof fn test1() {
            let tracked f = proof_fn|t: u8| {
                let mut a: int = 5;
                let tracked g = proof_fn|s: u8| {
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

        proof fn test1<T>(some_t: T) {
            let tracked f = proof_fn|t: T| -> (s: T)
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
        proof fn test(x: u8) {
            assert(x < 256);
            let tracked f = proof_fn|y: u8| {
                assert(x < 256);
                assert(y < 256);
            };
        }
    } => Ok(())
}

// type well-formed

test_verify_one_file_with_options! {
    #[test] error_msg_use_external_type_closure_param ["vstd"] => verus_code! {
        #[verifier(external)]
        struct X { }

        proof fn stuff() {
            let tracked f = proof_fn|x: X| { };
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use type `test_crate::X` which is ignored")
}

// Omitting error_msg_use_external_type_closure_ret because it uses a loop

test_verify_one_file_with_options! {
    #[test] right_decorations_for_tuple_arg ["vstd"] => verus_code! {
        use vstd::prelude::*;

        proof fn test<T: Copy, F>(s: &T, key: T, tracked less: proof_fn<F>(T, T) -> bool)
            where F: ProofFn + Copy
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

        proof fn test0<T: Copy, F>(left: T, right: T, tracked leq: &proof_fn<F>(T, T) -> bool)
            where F: ProofFn
            requires
                forall |x, y| #[trigger] leq.requires((x, y))
        {
            let x = leq(left, right);
        }

        proof fn moo() {
            let tracked t = proof_fn|| { };
            t();
        }

        proof fn stuff2<T: ProofFnOnce>(tracked t: proof_fn<T>() -> bool)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        proof fn moo2() {
            let tracked t = proof_fn|| -> (b: bool) ensures b == true { true };
            stuff2(t);
        }

        proof fn stuff3<T: ProofFn>(tracked t: proof_fn<T>() -> bool)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        proof fn moo3() {
            let tracked t = proof_fn|| -> (b: bool) ensures b == true { true };
            stuff3(t);
        }

        proof fn stuff4<T: ProofFn>(tracked t: &proof_fn<T>() -> bool)
            requires t.requires(()),
                !t.ensures((), false),
        {
            t();
        }

        proof fn moo4() {
            let tracked t = proof_fn|| -> (b: bool) ensures b == true { true };
            stuff4(&t);
        }
    } => Ok(())
}

// Omitting no_impl_fn_once because exec_closures.rs already checks FnOnce
// Omitting no_impl_fn_mut because exec_closures.rs already checks FnMut
// Omitting no_impl_fn because exec_closures.rs already checks Fn

test_verify_one_file_with_options! {
    // HACK: we ignore this test because Rust generates a long-type file for it,
    // because Rust's error message embeds the file system path of the .rs test file
    // in the string representation of closure type in the error.
    #[test] tracked_variables_captured_by_closures_send ["vstd"] => verus_code! {
        tracked struct X {
            rc: std::rc::Rc<u32>,
        }

        #[verifier::external_body]
        proof fn get_x() -> (tracked x: X) {
            unimplemented!();
        }

        proof fn require_send<T: Send>(t: T) { }

        proof fn test() {
            let tracked x = get_x();

            let tracked clos = move proof_fn[Send]|| {
                let tracked y = x;
                ()
            };

            require_send(clos);
        }
    } => Err(err) => assert_rust_error_msg(err, "`std::rc::Rc<u32>` cannot be sent between threads safely")
}

test_verify_one_file_with_options! {
    #[test] tracked_consume_nested_fn ["vstd"] => verus_code! {
        tracked struct X { }

        proof fn consume_x(tracked x: X) { }

        proof fn test() {
            let tracked x = X { };

            let tracked clos = move proof_fn|| {
                let tracked clos2 = move proof_fn|| {
                    let tracked y = x;
                    consume_x(y);
                };
            };

            consume_x(x);
        }
    } => Err(err) => assert_rust_error_msgs(err, &[
        "cannot move out of `x`, a captured variable in an `Fn` closure",
        "cannot move out of `x`, a captured variable in an `Fn` closure",
        "use of moved value: `x`"
    ])
}

test_verify_one_file_with_options! {
    #[test] tracked_consume_nested_fn_once ["vstd"] => verus_code! {
        tracked struct X { }

        proof fn consume_x(tracked x: X) { }

        proof fn test() {
            let tracked x = X { };

            let tracked clos = move proof_fn[Once]|| {
                let tracked clos2 = move proof_fn[Once]|| {
                    let tracked y = x;
                    consume_x(y);
                };
            };

            consume_x(x);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `x`")
}

test_verify_one_file_with_options! {
    #[test] tracked_consume_ghost ["vstd"] => verus_code! {
        tracked struct X { }

        proof fn consume_x(tracked x: X) { }

        proof fn ghost_x(x: X) { }

        proof fn test() {
            let tracked x = X { };

            let tracked clos = move proof_fn|| {
                let tracked clos2 = move proof_fn|| {
                    ghost_x(x);
                };
            };

            consume_x(x);
        }
    } => Ok(())
}

// <-------------------------------------------------
// End of tests were adapted from exec_closures.rs
/////////////////////////////////////////////////////

test_verify_one_file_with_options! {
    #[test] cant_implement_copy_trait ["vstd"] => verus_code! {
        impl Copy for FOpts<1, (), 0, 0, 0> {}
    } => Err(err) => assert_rust_error_msg(err, "only traits defined in the current crate can be implemented")
}

test_verify_one_file_with_options! {
    #[test] lifetime1 ["vstd"] => verus_code! {
        proof fn p(tracked f: proof_fn<'static>(u64) -> u64) {}
        proof fn q<'a>(tracked f: proof_fn<'a>(u64) -> u64) {
            p(f);
        }
    } => Err(err) => assert_rust_error_msg(err, "borrowed data escapes outside of function")
}

test_verify_one_file_with_options! {
    #[test] lifetime2 ["vstd"] => verus_code! {
        struct S;
        proof fn p<'a>(tracked f: proof_fn<'a>() -> tracked &'a S) {}
        proof fn q<'a>(tracked x: &'a S) {
            p(proof_fn|| -> tracked &'a S { x });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] lifetime3 ["vstd"] => verus_code! {
        struct S;
        proof fn p<'a>(tracked f: proof_fn<'static>() -> tracked &'a S) {}
        proof fn q<'a>(tracked x: &'a S) {
            p(proof_fn|| -> tracked &'a S { x });
        }
    } => Err(err) => assert_rust_error_msgs(err, &[
        "borrowed data escapes outside of function",
        "`x` does not live long enough",
    ])
}

test_verify_one_file_with_options! {
    #[test] lifetime5 ["vstd"] => verus_code! {
        struct S;
        proof fn p<'a>(tracked f: proof_fn<'a>() -> tracked &'static S) {}
        proof fn q<'a>(tracked x: &'a S) {
            p(proof_fn|| -> tracked &'a S { x });
        }
    } => Err(err) => assert_rust_error_msg(err, "borrowed data escapes outside of function")
}

test_verify_one_file_with_options! {
    #[test] lifetime6 ["vstd"] => verus_code! {
        struct S;
        proof fn p<'a>(tracked f: proof_fn<'a>() -> tracked &'static S) {}
        proof fn q<'a>(tracked x: &'a S) {
            p(proof_fn|| -> tracked &'static S { x });
        }
    } => Err(err) => assert_rust_error_msg(err, "lifetime may not live long enough")
}

test_verify_one_file_with_options! {
    #[test] copy1 ["vstd"] => verus_code! {
        proof fn p(tracked f1: proof_fn() -> u8, tracked f2: proof_fn() -> u8) {}
        proof fn q(tracked f: proof_fn() -> u8) {
            p(f, f);
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `f`")
}

test_verify_one_file_with_options! {
    #[test] copy2 ["vstd"] => verus_code! {
        proof fn p(tracked f1: proof_fn[Copy]() -> u8, tracked f2: proof_fn[Copy]() -> u8) {}
        proof fn q(tracked f: proof_fn[Copy]() -> u8) {
            p(f, f);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] copy3 ["vstd"] => verus_code! {
        proof fn p<F: Copy>(tracked f1: proof_fn<F>() -> u8, tracked f2: proof_fn<F>() -> u8) {}
        proof fn q<F: Copy>(tracked f: proof_fn<F>() -> u8) {
            p(f, f);
        }
        proof fn r(u: u8) {
            q(proof_fn[Copy]|| -> u8 { u });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] copy4 ["vstd"] => verus_code! {
        proof fn p<F: Copy>(tracked f1: proof_fn<F>() -> u8, tracked f2: proof_fn<F>() -> u8) {}
        proof fn q<F: Copy>(tracked f: proof_fn<F>() -> u8) {
            p(f, f);
        }
        proof fn r(u: u8) {
            q(proof_fn|| -> u8 { u });
        }
    } => Err(err) => assert_rust_error_msg(err, "Copy` is not satisfied")
}

test_verify_one_file_with_options! {
    #[test] copy5 ["vstd"] => verus_code! {
        struct S;
        proof fn p<F: Copy>(tracked f1: proof_fn<F>() -> S, tracked f2: proof_fn<F>() -> S) {}
        proof fn q<F: Copy>(tracked f: proof_fn<F>() -> S) {
            p(f, f);
        }
        proof fn r(s: S) {
            q(proof_fn[Copy]|| -> S { s });
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound `S: std::marker::Copy` is not satisfied in `{closure")
}

test_verify_one_file_with_options! {
    #[test] send1 ["vstd"] => verus_code! {
        proof fn p<T: Send>(tracked t: T) {}
        proof fn q<F>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn|| -> u8 { u });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot be sent between threads safely")
}

test_verify_one_file_with_options! {
    #[test] send2 ["vstd"] => verus_code! {
        proof fn p<T: Send>(tracked t: T) {}
        proof fn q<F: Send>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn|| -> u8 { u });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot be sent between threads safely")
}

test_verify_one_file_with_options! {
    #[test] send3 ["vstd"] => verus_code! {
        proof fn p<T: Send>(tracked t: T) {}
        proof fn q<F: Send>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn[Send]|| -> u8 { u });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] sync1 ["vstd"] => verus_code! {
        proof fn p<T: Sync>(tracked t: T) {}
        proof fn q<F>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn|| -> u8 { u });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot be shared between threads safely")
}

test_verify_one_file_with_options! {
    #[test] sync2 ["vstd"] => verus_code! {
        proof fn p<T: Sync>(tracked t: T) {}
        proof fn q<F: Sync>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn|| -> u8 { u });
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot be shared between threads safely")
}

test_verify_one_file_with_options! {
    #[test] sync3 ["vstd"] => verus_code! {
        proof fn p<T: Sync>(tracked t: T) {}
        proof fn q<F: Sync>(tracked f: proof_fn<F>() -> u8) {
            p(f);
        }
        proof fn r(u: u8) {
            q(proof_fn[Sync]|| -> u8 { u });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage1 ["vstd"] => verus_code! {
        proof fn q<F>(tracked f: proof_fn<F>() -> u8) {
            let u = f();
        }
    } => Err(err) => assert_rust_error_msg(err, "expected function, found")
}

test_verify_one_file_with_options! {
    #[test] usage2 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnOnce>(tracked f: proof_fn<F>() -> u8)
            requires f.requires(()),
        {
            let u = f();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage3 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnOnce>(tracked f: proof_fn<F>() -> u8)
            requires f.requires(()),
        {
            let u = f();
            let u = f();
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `f`")
}

test_verify_one_file_with_options! {
    #[test] usage4 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnMut>(tracked mut f: proof_fn<F>() -> u8)
            requires f.requires(()),
        {
            let u = f();
            let u = f();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage5 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFn>(tracked f: proof_fn<F>() -> u8)
            requires f.requires(()),
        {
            let u = f();
            let u = f();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage6 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnOnce>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn[Once]|| -> u8 { 5 });
            q(proof_fn[Mut]|| -> u8 { 5 });
            q(proof_fn|| -> u8 { 5 });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage7 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnMut>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn[Mut]|| -> u8 { 5 });
            q(proof_fn|| -> u8 { 5 });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage8 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFn>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn|| -> u8 { 5 });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] usage9 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFnMut>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn[Once]|| -> u8 { 5 });
        }
    } => Err(err) => assert_rust_error_msg(err, "verus_builtin::ProofFnMut` is not satisfied")
}

test_verify_one_file_with_options! {
    #[test] usage10 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFn>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn[Once]|| -> u8 { 5 });
        }
    } => Err(err) => assert_rust_error_msg(err, "verus_builtin::ProofFn` is not satisfied")
}

test_verify_one_file_with_options! {
    #[test] usage11 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        proof fn q<F: ProofFn>(tracked f: proof_fn<F>() -> u8) {}
        proof fn p() {
            q(proof_fn[Mut]|| -> u8 { 5 });
        }
    } => Err(err) => assert_rust_error_msg(err, "verus_builtin::ProofFn` is not satisfied")
}

test_verify_one_file_with_options! {
    #[test] reqens1 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        impl ProofFnReqEnsDef<(u8, u8), int> for S {
            open spec fn req(a: (u8, u8)) -> bool {
                a.0 < a.1
            }
            open spec fn ens(a: (u8, u8), o: int) -> bool {
                o == a.0 + a.1
            }
        }
        proof fn q1<F: ProofFn + ProofFnReqEns<S>>(tracked f: proof_fn<F>(u8, u8) -> int) {
            let x = f(10, 20);
            assert(x == 30);
        }
        proof fn q2<F: ProofFn + ProofFnReqEns<S>>(tracked f: proof_fn<F>(u8, u8) -> int) {
            f(20, 10); // FAILS
        }
        proof fn p1() {
            q1(proof_fn[ReqEns<S>]|x, y| { assert(x < y); x + y });
        }
        proof fn p2() {
            q1(proof_fn[ReqEns<S>]|x, y| { assert(x < y); x - y }); // FAILS
        }
        proof fn p3() {
            q1(proof_fn[ReqEns<S>]|x, y| { assert(x > y); x + y }); // FAILS
        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_one_file_with_options! {
    #[test] tracked_args1 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
        proof fn p(tracked s: S) {
            q(s, proof_fn|tracked x: S| -> tracked S { x });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] tracked_args2 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
        proof fn p(tracked s: S) {
            q(s, proof_fn|tracked x: S| -> S { x });
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file_with_options! {
    #[test] tracked_args3 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S) -> S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
        proof fn p(tracked s: S) {
            q(s, proof_fn|tracked x: S| -> S { x });
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args4 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
        proof fn p(tracked s: S) {
            q(s, proof_fn|tracked x: S| -> tracked S { x });
        }
    } => Err(err) => assert_rust_error_msg(err, "mismatched types")
}

test_verify_one_file_with_options! {
    #[test] tracked_args5 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
        proof fn p(tracked s: S) {
            q(s, proof_fn|x: S| -> tracked S { x });
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args6 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(s: S, tracked f: proof_fn<F>(tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args7 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S) -> S) -> tracked S
            requires forall|x: S| f.requires((x,)),
        {
            let tracked x = f(s);
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args8 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S, S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x, x)),
        {
            let y = s;
            let tracked x = f(s, y);
            x
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] tracked_args9 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S, tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x, x)),
        {
            let y = s;
            let tracked x = f(s, y);
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args10 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(S, tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x, x)),
        {
            let y = s;
            let tracked x = f(s, y);
            x
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file_with_options! {
    #[test] tracked_args11 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        struct S;
        proof fn q<F: ProofFn>(tracked s: S, tracked f: proof_fn<F>(tracked S, tracked S) -> tracked S) -> tracked S
            requires forall|x: S| f.requires((x, x)),
        {
            let tracked y = s;
            let tracked x = f(s, y);
            x
        }
    } => Err(err) => assert_rust_error_msg(err, "use of moved value: `s`")
}

test_verify_one_file_with_options! {
    #[test] tracked_recursive_type1 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        enum E<'a> {
            None,
            Some(tracked proof_fn<'a>[Once]() -> tracked E<'a>),
        }
        proof fn test() {
            let tracked e0 = E::None;
            let tracked e1 = E::Some(move proof_fn[Once]|| -> tracked E { e0 });
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] tracked_recursive_type2 ["vstd"] => verus_code! {
        use vstd::prelude::*;
        enum E<'a> {
            None,
            Some(proof_fn<'a>[Once](tracked E<'a>) -> ()),
        }
    } => Err(err) => assert_vir_error_msg(err, "E in a non-positive position")
}

test_verify_one_file_with_options! {
    #[test] output_param_covariant ["vstd"] => verus_code! {
        struct S;

        proof fn test<'a>(tracked f: proof_fn<'a>() -> tracked &'a S) {
        }

        proof fn test2<'a, 'b>(tracked f: proof_fn<'a>() -> tracked &'b S)
            where 'b: 'a
        {
            test(f);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] proof_fn_coerce_to_spec_issue2078 ["vstd"] => verus_code! {
        proof fn test() {
            let f = proof_fn|x: u32| { true };
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] proof_fn_call_spec ["vstd"] => verus_code! {
        proof fn test() {
            let f = proof_fn|x: u32| { true };
            f(12u32);
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}
