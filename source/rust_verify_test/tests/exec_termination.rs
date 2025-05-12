#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] recursive_exec_function_with_decreases_clause verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures r == i
            decreases i
        {
            if i == 0 {
                return 0;
            } else {
                return 1 + a(i - 1);
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] recursive_exec_function_with_decreases_clause_exec_allows_no_decreases_clause ["exec_allows_no_decreases_clause"] => verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures r == i
            decreases i
        {
            if i == 0 {
                return 0;
            } else {
                return 1 + a(i - 1);
            }
        }
    } => Ok(err) => assert!(err.warnings.iter().find(|x| x.message.contains("if exec_allows_no_decreases_clause is set, decreases checks in exec functions do not guarantee termination of functions with loops")).is_some())
}

test_verify_one_file_with_options! {
    #[test] recursive_exec_function_with_decreases_clause_exec_allows_no_decreases_clause_fails ["exec_allows_no_decreases_clause"] => verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures r == i
            decreases i
        {
            if i == 0 {
                return 0;
            } else {
                return a(i); // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] recursive_exec_function_needs_decreases_clause verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures r == i
        {
            if i == 0 {
                return 0;
            } else {
                return 1 + a(i - 1);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] mutually_recursive_exec_functions_need_decreases_clause verus_code! {
        fn dec1(i: u64) {
            if 0 < i { dec2(i, 100 * i); } // FAIL
        }
        fn dec2(j: u64, k: u64)
            decreases j, k
        {
            if 0 < k { dec2(j, k - 1); }
            if 0 < j {
                dec2(j - 1, 100 * j + k);
                dec1(j - 1);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] mutually_recursive_exec_functions_with_extra_dependency_need_decreases_clause verus_code! {
        fn dec1b(i: u64) {
            dec2b(i); // FAIL
        }
        #[verifier(external_body)]
        fn dec2b(i: u64) {
            extra_dependency(dec1b);
            unimplemented!();
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] mutually_recursive_exec_functions_in_different_modules_need_decreases_clause verus_code! {
        mod M1 {
            use builtin::*;
            pub(crate) fn f1(i: u64) -> u64 { crate::M2::f2(i - 1) } // FAIL
        }
        mod M2 {
            use builtin::*;
            pub(crate) fn f2(i: u64) -> u64 { crate::M1::f1(i - 1) }
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2);
        assert!(err.errors[0].code.is_none());
        assert!(err.errors[1].code.is_none());
        assert!(err.errors[0].message.contains("recursive function must have a decreases clause"));
        assert!(err.errors[1].message.contains("recursive function must have a decreases clause"));
    }
}

test_verify_one_file! {
    #[test] while_loop_needs_decreases_clause verus_code! {
        fn a() {
            let mut i = 0;
            while i < 10 // FAIL
                invariant i <= 10
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "loop must have a decreases clause")
}

test_verify_one_file! {
    #[test] nested_while_loops_need_decreases_clauses verus_code! {
        fn a() {
            let mut i = 0;
            let mut j = 0;
            while i < 10
                invariant
                    i <= 10,
                    j <= 5
                decreases
                    10 - i,
                {
                    i = i + 1;
                    while j < 5 // FAIL
                        invariant j <= 5
                        {
                            j = j + 1;
                        }
                }
        }
    } => Err(err) => assert_vir_error_msg(err, "loop must have a decreases clause")
}

test_verify_one_file! {
    #[test] loop_with_break_with_decreases_clause verus_code! {
        fn a() {
            let mut i: i8 = 0;
            loop
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
                decreases 10 - i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_with_break_need_decreases_clause verus_code! {
        fn a() {
            let mut i: i8 = 0;
            loop // FAIL
                invariant_except_break i <= 9
                invariant 0 <= i <= 10
                ensures 1 <= i
            {
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "loop must have a decreases clause")
}

test_verify_one_file! {
    #[test] for_loop_with_decreases_clause verus_code! {
        use vstd::prelude::*;
        fn a() {
            let mut i: i8 = 0;
            for x in iter: 0..10
                invariant i == iter.cur * 3,
                decreases 10 - iter.cur
            {
                i += 3;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] for_loop_2_with_decreases_clause verus_code! {
        use vstd::prelude::*;
        fn a() {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            for x in 0..10
                invariant i == x * 3,
                decreases 10 - x
            {
                i += 3;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] for_loop_doesnt_need_explicit_decreases_clause verus_code! {
        use vstd::prelude::*;
        fn a() {
            let mut i: i8 = 0;
            // syntax macro inserts decreases clause automatically
            for x in iter: 0..10
                invariant i == iter.cur * 3,
            {
                i += 3;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] nontermination_infinite_loop_allowed_with_attribute ["exec_allows_no_decreases_clause"] => verus_code! {
        fn a(i: u64) -> (r: u64)
            ensures false
        {
            loop {}
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] nontermination_infinite_loop_with_ghost_allowed_with_attribute ["exec_allows_no_decreases_clause"] => verus_code! {
        use vstd::modes::*;
        fn a() {
            let ghost mut a: int = 5;
            loop
                invariant a > 0
            {
                proof {
                    a = a + 1;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_recursive_function_with_while_loop_with_loop_isolation_false verus_code! {
        #[verifier::loop_isolation(false)]
        fn a(mut i: u64)
            requires i <= 10,
            decreases i,
        {
            let ghost initial_i = i;
            while 0 < i && i <= 10
                invariant
                    0 <= i <= 10,
                    i <= initial_i,
                decreases i,
            {
                a(i - 1);
                i -= 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_recursive_function_with_while_loop_assume_termination verus_code! {
        #[verifier::assume_termination]
        fn a(mut i: u64)
            requires i <= 10,
        {
            let ghost initial_i = i;
            while 0 < i && i <= 10
                invariant
                    0 <= i <= 10,
                    i <= initial_i,
            {
                a(i - 1);
                i -= 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_terminating_function_can_call_nonterminating_function verus_code! {
        fn a(mut i: u64) {
            while i > 0
                invariant 0 <= i,
                decreases i,
            {
                b();
                i -= 1;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn b() {
            loop { }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_termination_flag_1 verus_code! {
        fn a<AA: A>(mut i: u64) {
            while i > 0
                invariant 0 <= i,
                decreases i,
            {
                AA::b();
                i -= 1;
            }
        }

        trait A {
            #[verifier::exec_allows_no_decreases_clause]
            fn b();
        }
    } => Err(err) => assert_vir_error_msg(err, "trait method declaration cannot declare exec_allows_no_decreases_clause")
}

test_verify_one_file! {
    #[test] exec_termination_flag_2 verus_code! {
        trait A {
            fn b();
        }

        struct X { }

        impl A for X {
            #[verifier::exec_allows_no_decreases_clause]
            fn b() {
                loop { }
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] exec_termination_flag_3 ["exec_allows_no_decreases_clause"] => verus_code! {
        trait A {
            fn b();
        }

        struct X { }

        impl A for X {
            fn b() {
                loop { }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] exec_termination_flag_4 verus_code! {
        trait A {
            fn b();
        }

        struct X { }

        impl A for X {
            fn b() {
                loop { }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "loop must have a decreases clause")
}

test_verify_one_file! {
    #[test] exec_termination_flag_5 verus_code! {
        trait A {
            #[verifier::exec_allows_no_decreases_clause]
            fn b() {
                loop { }
            }
        }
    } => Ok(())
}
