#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] control_flow_loops ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref));
            assert(x == 20);

            loop {
                if some_bool() { break; }

                assert(has_resolved(x_ref));
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            loop {
                if some_bool() { break; }

                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            loop {
                if some_bool() { break; }

                *x_ref = 20;

                assert(has_resolved(x_ref)); // FAILS
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop4() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            loop {
                if some_bool() {
                    assert(has_resolved(x_ref));
                    //assert(x == 20); // TODO(new_mut_ref): presently no way to specify the invariant we need
                    break;
                }

                *x_ref = 20;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop5() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            loop {
                if some_bool() {
                    assert(has_resolved(x_ref)); // FAILS
                    continue;
                }

                *x_ref = 20;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop6() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            loop {
                if some_bool() {
                    assert(has_resolved(x_ref)); // FAILS
                    break;
                }
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop7() {
            loop {
                if some_bool() {
                    break;
                }

                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop8() {
            loop {
                if some_bool() {
                    break;
                }

                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);

                continue;
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] control_flow_loops_nested ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested() {
            let mut x = 0;
            let mut x_ref = &mut x;

            loop {
                if some_bool() { break; }

                loop {
                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            break;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            'a: loop {
                if some_bool() { break; }

                loop {
                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            break 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            loop {
                if some_bool() { break; }

                'b: loop {
                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            break 'b;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested4() {
            loop {
                if some_bool() { break; }

                loop {
                    let mut x = 0;
                    let mut x_ref = &mut x;

                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            continue;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested5() {
            'a: loop {
                if some_bool() { break; }

                loop {
                    let mut x = 0;
                    let mut x_ref = &mut x;

                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested6() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            loop {
                if some_bool() { break; }

                loop {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            continue;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested7() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            loop {
                if some_bool() { break; }

                loop {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            break;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested8() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            loop {
                if some_bool() { break; }

                'b: loop {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    loop {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'b;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested9() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            'a: loop {
                if some_bool() { break; }

                'b: loop {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    'c: loop {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] control_flow_while_loops ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref));
            assert(x == 20);

            while some_bool() {
                assert(has_resolved(x_ref));
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            while some_bool() {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            while some_bool() {
                *x_ref = 20;

                assert(has_resolved(x_ref)); // FAILS
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop4() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            while some_bool() {
                if some_bool() {
                    assert(has_resolved(x_ref));
                    //assert(x == 20); // TODO(new_mut_ref): presently no way to specify the invariant we need
                    break;
                }

                *x_ref = 20;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop5() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            while some_bool() {
                if some_bool() {
                    assert(has_resolved(x_ref)); // FAILS
                    continue;
                }

                *x_ref = 20;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop6() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            while some_bool() {
                if some_bool() {
                    assert(has_resolved(x_ref)); // FAILS
                    break;
                }
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop7() {
            while some_bool() {
                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop8() {
            while some_bool() {
                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);

                continue;
            }
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] loop_vs_while_loop ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unreachable_code)]
        fn loop1() {
            let mut x = 24;
            let x_ref = &mut x;

            loop {
                assert(has_resolved(x_ref));
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 24;
            let x_ref = &mut x;

            while some_bool() {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] loops_resolve_depends_on_condition_branch ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x = 24;
            let x_ref = &mut x;

            while some_bool()
                invariant has_resolved(x_ref) // FAILS
            {
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 24;
            let x_ref = &mut x;

            while some_bool()
                invariant has_resolved(x_ref) // FAILS
            {
                *x_ref = 20;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x = 24;
            let x_ref = &mut x;

            // to get this one to work, the analysis needs to insert assume(has_resolved(...))
            // at odd point in the expression tree: right after the condition,
            // but only when it evaluates to false.
            while some_bool()
                ensures has_resolved(x_ref)
            {
                *x_ref = 20;
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file_with_options! {
    #[test] loops_resolve_depends_on_condition_branch2 ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn get_mut_ref<'a>() -> &'a mut u64 { loop { } }

        // It seems like these ought to work, but don't quite work because the order of operations
        // is:
        //   - assert invariant holds
        //   - evaluation condition
        //   - branch on condition
        // And our analysis can only insert the `assume(has_resolved(...))` expressions
        // after the branch. So the assume necessarily comes after the assert.

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::loop_isolation(false)]
        fn loop4() {
            let mut x = 24;
            let x_ref = &mut x;
            let mut b = some_bool();

            while b
                invariant !b ==> has_resolved(x_ref) // FAILS
            {
                *x_ref = 20;
                b = some_bool();
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::loop_isolation(true)]
        fn loop4_loop_iso() {
            let mut x = 24;
            let x_ref = &mut x;
            let mut b = some_bool();

            while b
                invariant !b ==> has_resolved(x_ref) // FAILS
            {
                *x_ref = 20;
                b = some_bool();
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::loop_isolation(false)]
        fn loop5() {
            let mut x = 24;
            let mut x_ref = &mut x;
            let mut b = some_bool();

            while b
                invariant b ==> has_resolved(x_ref) // FAILS
            {
                x_ref = get_mut_ref();
                b = some_bool();
            }

            *x_ref = 20;
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::loop_isolation(true)]
        fn loop5_loop_iso() {
            let mut x = 24;
            let mut x_ref = &mut x;
            let mut b = some_bool();

            while b
                invariant b ==> has_resolved(x_ref) // FAILS
            {
                x_ref = get_mut_ref();
                b = some_bool();
            }

            *x_ref = 20;
        }

    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file_with_options! {
    #[test] control_flow_while_loops_nested ["new-mut-ref"] => verus_code! {
        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested() {
            let mut x = 0;
            let mut x_ref = &mut x;

            while some_bool() {
                while some_bool() {
                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            break;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            'a: while some_bool() {
                while some_bool() {
                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            break 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            while some_bool() {
                'b: while some_bool() {
                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            break 'b;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested4() {
            while some_bool() {
                loop {
                    let mut x = 0;
                    let mut x_ref = &mut x;

                    if some_bool() { break; }

                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            continue;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested5() {
            'a: while some_bool() {
                loop {
                    let mut x = 0;
                    let mut x_ref = &mut x;

                    if some_bool() { break; }

                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested6() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            while some_bool() {
                while some_bool() {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref)); // FAILS
                            continue;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested7() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            while some_bool() {
                while some_bool() {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            break;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn nested8() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            while some_bool() {
                'b: while some_bool() {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'b;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[allow(unused_labels)]
        fn nested9() {
            let mut x = 0;
            let mut y = 0;
            let mut x_ref = &mut x;

            'a: while some_bool() {
                'b: while some_bool() {
                    x_ref = &mut y;

                    if some_bool() { break; }

                    'c: while some_bool() {
                        if some_bool() {
                            assert(has_resolved(x_ref));
                            continue 'a;
                        }

                        *x_ref = 20;
                    }
                }
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] for_loops ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn some_bool() -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref));
            assert(x == 20);

            for i in 0 .. 10 {
                assert(has_resolved(x_ref));
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            for i in 0 .. 10 {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            for i in 0 .. 10 {
                *x_ref = 20;

                assert(has_resolved(x_ref)); // FAILS
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop7() {
            for i in 0 .. 10 {
                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);
            }
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] for_loops_loop_isolation_false ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn some_bool() -> bool { true }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref));
            assert(x == 20);

            for i in 0 .. 10 {
                assert(has_resolved(x_ref));
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            for i in 0 .. 10 {
            }

            *x_ref = 20;

            assert(has_resolved(x_ref));
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop2_2() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            for i in 0 .. 10 {
                assert(has_resolved(x_ref)); // FAILS
            }

            *x_ref = 20;

            assert(has_resolved(x_ref));
        }


        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            assert(has_resolved(x_ref)); // FAILS

            for i in 0 .. 10 {
                *x_ref = 20;

                assert(has_resolved(x_ref)); // FAILS
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop4() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            for i in 0 .. 10 {
                if some_bool() {
                    assert(has_resolved(x_ref));
                    //assert(x == 20); // TODO(new_mut_ref): presently no way to specify the invariant we need
                    break;
                }

                *x_ref = 20;
            }
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop6() {
            let mut x = 0;
            let mut x_ref = &mut x;

            *x_ref = 20;

            for i in 0 .. 10 {
                if some_bool() {
                    assert(has_resolved(x_ref)); // FAILS
                    break;
                }
            }

            *x_ref = 20;
        }

        #[verifier::loop_isolation(false)]
        #[verifier::exec_allows_no_decreases_clause]
        fn loop7() {
            for i in 0 .. 10 {
                let mut x = 0;
                let mut x_ref = &mut x;

                *x_ref = 20;

                assert(has_resolved(x_ref));
                assert(x == 20);
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] while_loops_with_mutation_in_condition ["new-mut-ref"] => verus_code! {
        fn some_bool(x: &mut u64) -> bool { true }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop1() {
            let mut x: u64 = 0;
            let x_ref = &mut x;

            while some_bool(x_ref) {
                assert(has_resolved(x_ref)); // FAILS
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop2() {
            let mut x: u64 = 0;
            let x_ref = &mut x;

            while some_bool(x_ref) {
                assert(has_resolved(x_ref));
                break;
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop3() {
            let mut x: u64 = 0;
            let x_ref = &mut x;

            while ({
                assert(has_resolved(x_ref)); // FAILS
                some_bool(x_ref)
            }) {
                break;
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop4() {
            let mut x: u64 = 0;
            let x_ref = &mut x;

            while ({
                let b = some_bool(x_ref);
                assert(has_resolved(x_ref));
                b
            }) {
                break;
            }

            assert(has_resolved(x_ref));
        }

        #[verifier::exec_allows_no_decreases_clause]
        fn loop5() {
            let mut x: u64 = 0;
            let x_ref = &mut x;

            let mut y: u64 = 0;
            let y_ref = &mut y;

            while ({
                assert(has_resolved(x_ref));
                some_bool(y_ref)
            }) {
                break;
            }

            assert(has_resolved(x_ref));
        }
    } => Err(err) => assert_fails(err, 2)
}
