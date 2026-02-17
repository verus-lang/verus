#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] slice_basic ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_assign_slice_box(x: Box<[u64]>)
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let mut x = x;
            x[1] = 20;
            assert((*x)@ =~= seq![5u64, 20, 8]);
        }

        fn fail_assign_slice_box(x: Box<[u64]>)
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let mut x = x;
            x[1] = 20;
            assert((*x)@ =~= seq![5u64, 20, 8]);
            assert(false); // FAILS
        }

        fn test_assign_slice_mut_ref(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
        }

        fn fail_assign_slice_mut_ref(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_assign_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[1].1 = 200;
            assert(x.0@ =~= seq![(5u64, 6), (7, 200), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_assign_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[1].1 = 200;
            assert(x.0@ =~= seq![(5u64, 6), (7, 200), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_mut_ref_of_slice_index(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let x_ref = &mut x[1];
            *x_ref = 20;
            assert((*x)@ =~= seq![5, 20, 8]);
        }

        fn fail_mut_ref_of_slice_index(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let x_ref = &mut x[1];
            *x_ref = 20;
            assert((*x)@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_match_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (ref mut x_ref, ref mut y_ref) => {
                    *x_ref = 20;
                    *y_ref = 30;
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (20, 30), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_match_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (ref mut x_ref, ref mut y_ref) => {
                    *x_ref = 20;
                    *y_ref = 30;
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (20, 30), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_match_copy_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (a, b) => {
                    assert(a == 7);
                    assert(b == 8);
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (7, 8), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_match_copy_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (a, b) => {
                    assert(a == 7);
                    assert(b == 8);
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (7, 8), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_shr_bor_slice(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[1].0;
            assert(y == 7);
        }

        fn fail_shr_bor_slice(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[1].0;
            assert(y == 7);
            assert(false); // FAILS
        }

        struct Pair<A, B> { a: A, b: B }

        fn test_ctor_update_fail_slice(x: &mut [Pair<u64, u64>])
            requires x@ == seq![Pair { a: 0u64, b: 1u64 }, Pair { a: 2, b: 3 }, Pair { a: 4, b: 5 }]
        {
            let y = Pair::<u64, u64> { a: 13, .. (*x)[1] };
            assert(y.a == 13 && y.b == 3);
        }

        fn fail_ctor_update_fail_slice(x: &mut [Pair<u64, u64>])
            requires x@ == seq![Pair { a: 0u64, b: 1u64 }, Pair { a: 2, b: 3 }, Pair { a: 4, b: 5 }]
        {
            let y = Pair::<u64, u64> { a: 13, .. (*x)[1] };
            assert(y.a == 13 && y.b == 3);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file_with_options! {
    #[test] array_basic ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_assign_array() {
            let mut x: [u64; 3] = [5, 7, 8];
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
        }

        fn fail_assign_array() {
            let mut x: [u64; 3] = [5, 7, 8];
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_assign_mut_ref_array(x: &mut [u64; 3])
            requires mut_ref_current(x)@ == seq![5u64, 7, 8],
        {
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
        }

        fn fail_assign_mut_ref_array(x: &mut [u64; 3])
            requires mut_ref_current(x)@ == seq![5u64, 7, 8],
        {
            x[1] = 20;
            assert(x@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_assign_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                mut_ref_current(x.0)@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                mut_ref_current(x.1)@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[1].1 = 200;
            assert(x.0@ =~= seq![(5u64, 6), (7, 200), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_assign_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                mut_ref_current(x.0)@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                mut_ref_current(x.1)@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[1].1 = 200;
            assert(x.0@ =~= seq![(5u64, 6), (7, 200), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let x_ref = &mut x[1];
            *x_ref = 20;
            assert(x@ =~= seq![5, 20, 8]);
        }

        fn fail_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let x_ref = &mut x[1];
            *x_ref = 20;
            assert(x@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_let_decl_pattern_match_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let ref mut x_ref = x[1];
            *x_ref = 20;
            assert(x@ =~= seq![5, 20, 8]);
        }

        fn fail_let_decl_pattern_match_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let ref mut x_ref = x[1];
            *x_ref = 20;
            assert(x@ =~= seq![5, 20, 8]);
            assert(false); // FAILS
        }

        fn test_match_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (ref mut x_ref, ref mut y_ref) => {
                    *x_ref = 20;
                    *y_ref = 30;
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (20, 30), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_match_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (ref mut x_ref, ref mut y_ref) => {
                    *x_ref = 20;
                    *y_ref = 30;
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (20, 30), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_match_copy_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (a, b) => {
                    assert(a == 7);
                    assert(b == 8);
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (7, 8), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
        }

        fn fail_match_copy_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[1] {
                (a, b) => {
                    assert(a == 7);
                    assert(b == 8);
                }
            }
            assert(x.0@ =~= seq![(5u64, 6), (7, 8), (9, 10)]);
            assert(x.1@ =~= seq![(11u64, 12), (13, 14), (15, 16)]);
            assert(false); // FAILS
        }

        fn test_shr_bor_array(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[1].0;
            assert(y == 7);
        }

        fn fail_shr_bor_array(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[1].0;
            assert(y == 7);
            assert(false); // FAILS
        }

        struct Pair<A, B> { a: A, b: B }

        fn test_ctor_update_fail_array(x: &mut [Pair<u64, u64>; 3])
            requires x@ == seq![Pair { a: 0u64, b: 1u64 }, Pair { a: 2, b: 3 }, Pair { a: 4, b: 5 }]
        {
            let y = Pair::<u64, u64> { a: 13, .. (*x)[1] };
            assert(y.a == 13 && y.b == 3);
        }

        fn fail_ctor_update_fail_array(x: &mut [Pair<u64, u64>; 3])
            requires x@ == seq![Pair { a: 0u64, b: 1u64 }, Pair { a: 2, b: 3 }, Pair { a: 4, b: 5 }]
        {
            let y = Pair::<u64, u64> { a: 13, .. (*x)[1] };
            assert(y.a == 13 && y.b == 3);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file_with_options! {
    #[test] slice_overflow ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn overflow_assign_slice_box(x: Box<[u64]>)
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let mut x = x;
            x[100] = 20; // FAILS
        }

        fn overflow_assign_slice_mut_ref(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            x[3] = 20; // FAILS
        }

        fn overflow_assign_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[13].1 = 200; // FAILS
        }

        fn overflow_mut_ref_of_slice_index(x: &mut [u64])
            requires (*x)@ == seq![5u64, 7, 8],
        {
            let x_ref = &mut x[3]; // FAILS
        }

        fn overflow_match_mut_ref_slice_nested(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[3] // FAILS
            {
                (ref mut x_ref, ref mut y_ref) => { }
            }
        }

        fn overflow_shr_bor_slice(x: (&mut [(u64, u64)], &mut [(u64, u64)]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[3].0; // FAILS
        }

        struct Triple<A, B, C> { a: A, b: B, c: C }

        fn overflow_ctor_update_fail_slice(x: &mut [Triple<u64, u64, u64>])
            requires x@ == seq![Triple { a: 0u64, b: 1u64, c: 100u64 }, Triple { a: 2, b: 3, c: 101u64 }, Triple { a: 4, b: 5, c: 101 }]
        {
            let y = Triple::<u64, u64, u64> { a: 13, .. (*x)[3] }; // FAILS
        }
    } => Err(err) => assert_fails(err, 7)
}

test_verify_one_file_with_options! {
    #[test] array_overflow ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn overflow_assign_array() {
            let mut x: [u64; 3] = [5, 7, 8];
            x[3] = 20; // FAILS
        }

        fn overflow_assign_mut_ref_array(x: &mut [u64; 3])
            requires mut_ref_current(x)@ == seq![5u64, 7, 8],
        {
            x[3] = 20; // FAILS
        }

        fn overflow_assign_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                mut_ref_current(x.0)@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                mut_ref_current(x.1)@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            x.0[3].1 = 200; // FAILS
        }


        fn overflow_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let x_ref = &mut x[3]; // FAILS
        }

        fn overflow_let_decl_pattern_match_mut_ref_of_array_index() {
            let mut x: [u64; 3] = [5, 7, 8];
            let ref mut x_ref = x[3]; // FAILS
        }

        fn overflow_match_mut_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[3] // FAILS
            {
                (ref mut x_ref, ref mut y_ref) => {
                }
            }
        }

        fn overflow_match_copy_ref_array_nested(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            match x.0[3] // FAILS
            {
                (a, b) => { }
            }
        }

        fn overflow_shr_bor_array(x: (&mut [(u64, u64); 3], &mut [(u64, u64); 3]))
            requires
                x.0@ == seq![(5u64, 6u64), (7, 8), (9, 10)],
                x.1@ == seq![(11u64, 12u64), (13, 14), (15, 16)],
        {
            let y = &x.0[3].0; // FAILS
        }

        struct Triple<A, B, C> { a: A, b: B, c: C }

        fn overflow_ctor_update_fail_array(x: &mut [Triple<u64, u64, u64>; 3])
            requires x@ == seq![Triple { a: 0u64, b: 1u64, c: 100u64 }, Triple { a: 2, b: 3, c: 101u64 }, Triple { a: 4, b: 5, c: 101 }]
        {
            let y = Triple::<u64, u64, u64> { a: 13, .. (*x)[3] }; // FAILS
        }
    } => Err(err) => assert_fails(err, 9)
}

test_verify_one_file_with_options! {
    #[test] idx_nonproph ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::prophetic]
        uninterp spec fn idx<A>() -> A;

        fn test(x: &mut [u64; 3]) {
            proof {
                // this doesn't work because this index operator turns into spec_index
                // but conceivably this could be valid syntax
                // (which would then need to fail because the idx is prophetic)
                x[idx()] = 3;
            }
        }
    } => Err(err) => assert_rust_error_msg(err, "invalid left-hand side of assignment")
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_mut_ref_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 5);
            assert(a == 23);
        }

        fn fail_mut_ref_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 5);
            assert(a == 23);
            assert(false); // FAILS
        }

        fn test_mut_ref_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 0); // we mutated a temporary, not x, so x remains the same
            assert(a == 123);
        }

        fn fail_mut_ref_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 0); // we mutated a temporary, not x, so x remains the same
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_assign_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 5);
            assert(a == 23);
        }

        fn fail_assign_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 5);
            assert(a == 23);
            assert(false); // FAILS
        }

        fn test_assign_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 0);
            assert(a == 123);
        }

        fn fail_assign_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 0);
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_assign_op_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 5);
            assert(a == 23);
        }

        fn fail_assign_op_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 5);
            assert(a == 23);
            assert(false); // FAILS
        }

        fn test_assign_op_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 0);
            assert(a == 123);
        }

        fn fail_assign_op_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 0);
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_match_1() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (20, 30));
            assert(a == 23);
        }

        fn fail_match_1() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (20, 30));
            assert(a == 23);
            assert(false); // FAILS
        }

        fn test_match_2() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (0, 1));
            assert(a == 123);
        }

        fn fail_match_2() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (0, 1));
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_read_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 23);
        }

        fn fail_read_1() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = x[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 23);
            assert(false); // FAILS
        }

        fn test_read_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 123);
        }

        fn fail_read_2() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = ({a = 10*a + 1; x})[{a = 10*a + 2; 0}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 123);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 10)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering2 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_mut_ref() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 0); // we mutated a temporary, not x, so x remains the same
            assert(a == 123);
        }

        fn fail_mut_ref() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}];
            *z = 5;

            assert(x[0][0] == 0); // we mutated a temporary, not x, so x remains the same
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_assign() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 0);
            assert(a == 123);
        }

        fn fail_assign() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] = 5;

            assert(x[0][0] == 0);
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_assign_op() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 0);
            assert(a == 123);
        }

        fn fail_assign_op() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] += 5;

            assert(x[0][0] == 0);
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_match() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (0, 1));
            assert(a == 123);
        }

        fn fail_match() {
            let mut a = 0;
            let mut x: [[(u64, u64); 2]; 2] = [[(0, 1), (2, 3)], [(4, 5), (6, 7)]];

            match ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}] {
                (ref mut p1, ref mut p2) => {
                    *p1 = 20;
                    *p2 = 30;
                }
            }

            assert(x[0][0] === (0, 1));
            assert(a == 123);
            assert(false); // FAILS
        }

        fn test_read() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 123);
        }

        fn fail_read() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = ({a = 10*a + 1; x})[{a = 10*a + 2; a-12}][{a = 10*a + 3; 0}];
            assert(z == 0);

            assert(a == 123);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 5)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering3 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        // Assignments and primtive-compound-assignments are evaluated RHS first!

        fn test() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 0;
            x[0][a] = ({ a = a + 1; 5 });
            assert(x[0][0] == 0 && x[0][1] == 5 && x[1][0] == 2 && x[1][1] == 3);
        }

        fn fails() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 0;
            x[0][a] = ({ a = a + 1; 5 });
            assert(x[0][0] == 0 && x[0][1] == 5 && x[1][0] == 2 && x[1][1] == 3);
            assert(false); // FAILS
        }

        fn test_assign_op() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 0;
            x[0][a] += ({ a = a + 1; 5 });
            assert(x[0][0] == 0 && x[0][1] == 6 && x[1][0] == 2 && x[1][1] == 3);
        }

        fn fails_assign_op() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 0;
            x[0][a] += ({ a = a + 1; 5 });
            assert(x[0][0] == 0 && x[0][1] == 6 && x[1][0] == 2 && x[1][1] == 3);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering4 ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 10;
            x[0][({ a = 11; 0 })] = a;
            assert(x[0][0] == 10 && x[0][1] == 1 && x[1][0] == 2 && x[1][1] == 3);
        }

        fn fails() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 10;
            x[0][({ a = 11; 0 })] = a;
            assert(x[0][0] == 10 && x[0][1] == 1 && x[1][0] == 2 && x[1][1] == 3);
            assert(false); // FAILS
        }

        fn test_assign_op() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 10;
            x[0][({ a = 11; 0 })] += a;
            assert(x[0][0] == 10 && x[0][1] == 1 && x[1][0] == 2 && x[1][1] == 3);
        }

        fn fails_assign_op() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            let mut a = 10;
            x[0][({ a = 11; 0 })] += a;
            assert(x[0][0] == 10 && x[0][1] == 1 && x[1][0] == 2 && x[1][1] == 3);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering5 ["new-mut-ref"] => verus_code! {
        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                loop { }
                0
            })] = ({
                5
            });
            assert(false);
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test2() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                0
            })] = ({
                loop { }
                5
            });
            assert(false);
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test3() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                assert(false);
                0
            })] = ({
                loop { }
                5
            });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test4() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                assert(false); // FAILS
                loop { }
                0
            })] = ({
                5
            });
        }

        #[allow(unreachable_code)]
        #[verifier::exec_allows_no_decreases_clause]
        fn test5() {
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                loop { }
                0
            })] = ({
                assert(false); // FAILS
                5
            });
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering_overflow_error ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 0;
            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];

            let z = &mut ({a = 20; x})[a][{a = 0; 0}]; // FAILS
            *z = 5;
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering_rhs_first_resolution_inf ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                assert(has_resolved(y_ref));
                0
            })] = ({
                *y_ref = 101;
                5
            });
            assert(y == 101);
        }

        fn test2() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] = ({
                assert(has_resolved(y_ref)); // FAILS
                5
            });
        }

        fn test3() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] = ({
                *y_ref = 102;
                5
            });
            assert(y == 101);
        }

        fn fails3() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] = ({
                *y_ref = 102;
                5
            });
            assert(y == 101);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] control_flow_ordering_rhs_first_resolution_inf_compound ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                assert(has_resolved(y_ref));
                0
            })] += ({
                *y_ref = 101;
                5
            });
            assert(y == 101);
        }

        fn test2() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] += ({
                assert(has_resolved(y_ref)); // FAILS
                5
            });
        }

        fn test3() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] += ({
                *y_ref = 102;
                5
            });
            assert(y == 101);
        }

        fn fails3() {
            let mut y = 100;
            let y_ref = &mut y;

            let mut x: [[u64; 2]; 2] = [[0, 1], [2, 3]];
            x[0][({
                *y_ref = 101;
                0
            })] += ({
                *y_ref = 102;
                5
            });
            assert(y == 101);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] array_of_mut_refs ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_array() {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let mut x: [&mut u64; 3] = [&mut a, &mut b, &mut c];

            *x[0] = 10;
            *x[1] = 11;
            *x[2] = 12;

            x[2] = &mut d;

            *x[2] = 13;

            assert(has_resolved(x[0]));
            assert(has_resolved(x[1]));
            assert(has_resolved(x[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
            assert(d == 13);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] slice_of_mut_refs ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_slice(x: Box<[&mut u64]>)
            requires x@.len() == 3
        {
            let mut a = 0;
            let mut b = 1;
            let mut c = 2;
            let mut d = 3;

            let mut x = x;
            x[0] = &mut a;
            x[1] = &mut b;
            x[2] = &mut c;

            *x[0] = 10;
            *x[1] = 11;
            *x[2] = 12;

            x[2] = &mut d;

            *x[2] = 13;

            assert(has_resolved(x[0]));
            assert(has_resolved(x[1]));
            assert(has_resolved(x[2]));

            assert(a == 10);
            assert(b == 11);
            assert(c == 12);
            assert(d == 13);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] slices_lib_first_last_mut ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_emp() {
            let v: Vec<u64> = vec![];
            let f = v.first();
            assert(f === None);
            let l = v.last();
            assert(l === None);
        }

        fn test_non_emp() {
            let v = vec![1, 2, 3];
            let f = v.first();
            assert(f === Some(&1));
            let l = v.last();
            assert(l === Some(&3));
        }

        fn test_emp_first_mut() {
            let mut v: Vec<u64> = vec![];
            let f = v.as_mut_slice().first_mut();
            assert(f === None);
            assert(v@ === seq![]);
        }

        fn test_emp_last_mut() {
            let mut v: Vec<u64> = vec![];
            let f = v.as_mut_slice().last_mut();
            assert(f === None);
            assert(v@ === seq![]);
        }

        fn test_non_emp_first_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let f = v.as_mut_slice().first_mut();
            assert(f.is_some());
            let m = f.unwrap();
            assert(*m == 1);
            *m = 10;
            assert(v@ === seq![10, 2, 3]);
        }

        fn test_non_emp_last_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let f = v.as_mut_slice().last_mut();
            assert(f.is_some());
            let m = f.unwrap();
            assert(*m == 3);
            *m = 10;
            assert(v@ === seq![1, 2, 10]);
        }

        fn fail_emp() {
            let v: Vec<u64> = vec![];
            let f = v.first();
            assert(f === None);
            let l = v.last();
            assert(l === None);
            assert(false); // FAILS
        }

        fn fail_non_emp() {
            let v = vec![1, 2, 3];
            let f = v.first();
            assert(f === Some(&1));
            let l = v.last();
            assert(l === Some(&3));
            assert(false); // FAILS
        }

        fn fail_emp_first_mut() {
            let mut v: Vec<u64> = vec![];
            let f = v.as_mut_slice().first_mut();
            assert(f === None);
            assert(v@ === seq![]);
            assert(false); // FAILS
        }

        fn fail_emp_last_mut() {
            let mut v: Vec<u64> = vec![];
            let f = v.as_mut_slice().last_mut();
            assert(f === None);
            assert(v@ === seq![]);
            assert(false); // FAILS
        }

        fn fail_non_emp_first_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let f = v.as_mut_slice().first_mut();
            assert(f.is_some());
            let m = f.unwrap();
            assert(*m == 1);
            *m = 10;
            assert(v@ === seq![10, 2, 3]);
            assert(false); // FAILS
        }

        fn fail_non_emp_last_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let f = v.as_mut_slice().last_mut();
            assert(f.is_some());
            let m = f.unwrap();
            assert(*m == 3);
            *m = 10;
            assert(v@ === seq![1, 2, 10]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] slices_lib_split_at ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test_split_at() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(2);
            assert(a@ === seq![1, 2]);
            assert(b@ === seq![3]);
        }

        fn test_split_at_end() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(3);
            assert(a@ === seq![1, 2, 3]);
            assert(b@ === seq![]);
        }

        fn test_split_at_out_of_bounds() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(4); // FAILS
        }

        fn test_split_at_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.as_mut_slice().split_at_mut(2);
            assert(a@ === seq![1, 2]);
            assert(b@ === seq![3]);
            a[1] = 20;
            b[0] = 30;
            assert(v@ === seq![1, 20, 30]);
        }

        fn test_split_at_mut_end() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.as_mut_slice().split_at_mut(3);
            assert(a@ === seq![1, 2, 3]);
            assert(b@ === seq![]);
            a[1] = 20;
            assert(v@ === seq![1, 20, 3]);
        }

        fn test_split_at_mut_out_of_bounds() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(4); // FAILS
        }

        fn fail_split_at() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(2);
            assert(a@ === seq![1, 2]);
            assert(b@ === seq![3]);
            assert(false); // FAILS
        }

        fn fail_split_at_end() {
            let v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.split_at(3);
            assert(a@ === seq![1, 2, 3]);
            assert(b@ === seq![]);
            assert(false); // FAILS
        }

        fn fail_split_at_mut() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.as_mut_slice().split_at_mut(2);
            assert(a@ === seq![1, 2]);
            assert(b@ === seq![3]);
            a[1] = 20;
            b[0] = 30;
            assert(v@ === seq![1, 20, 30]);
            assert(false); // FAILS
        }

        fn fail_split_at_mut_end() {
            let mut v: Vec<u64> = vec![1, 2, 3];
            let (a, b) = v.as_mut_slice().split_at_mut(3);
            assert(a@ === seq![1, 2, 3]);
            assert(b@ === seq![]);
            a[1] = 20;
            assert(v@ === seq![1, 20, 3]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 6)
}

test_verify_one_file_with_options! {
    #[test] slices_assign_resolving_basic ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        spec fn id<A>(a: A) -> A { a }

        fn test_slice0(x: Box<[&mut u64]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;

            // In principle this is fine, but the current alg won't put it this early
            // for index places.
            assert(has_resolved(x[0])); // FAILS

            x[0] = &mut a;
        }

        fn test_slice1(x: Box<[&mut u64]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x[0]);
            x[0] = &mut a;
            assert(has_resolved(g));
        }

        fn test_slice2(x: Box<[[&mut u64; 2]]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x[0][1]);
            x[0][1] = &mut a;
            assert(has_resolved(g));
        }

        fn test_slice_field(x: Box<[(&mut u64, &mut u64)]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x[0].1);
            x[0].1 = &mut a;
            assert(has_resolved(g));
        }

        fn test_slice_field_fails(x: Box<[(&mut u64, &mut u64)]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x[0].0);
            x[0].1 = &mut a;
            assert(has_resolved(g)); // FAILS
        }

        fn test_slice_field_fails2(x: Box<[(&mut u64, &mut u64)]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x[0]);
            x[0].1 = &mut a;
            assert(has_resolved(g)); // FAILS
        }

        fn test_slice_field_fails3(x: Box<[(&mut u64, &mut u64)]>)
            requires x.len() > 0
        {
            let mut x = x;
            let mut a = 5;
            let ghost g = id(x);
            x[0].1 = &mut a;
            assert(has_resolved(g)); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file_with_options! {
    #[test] new_mut_ref ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn consume<A>(a: A) { }

        fn test(a: &mut [u64]) {
            // TODO(new_mut_ref): export an axiom so this succeeds
            // (note: this might be tricky to do in a sound way, since the AIR encoding
            // lets you assign anything to current?)
            assert(a@.len() == fin(a)@.len()); // FAILS
            consume(a);
        }

        fn test2(a: &mut Box<[u64]>) {
            // This one must fail, though:
            assert(a@.len() == fin(a)@.len()); // FAILS
            consume(a);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file_with_options! {
    #[test] mut_ref_unsizing_coercion ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a: [u64; 3] = [0, 1, 2];
            let a_ref: &mut [u64; 3] = &mut a;
            let a_ref2: &mut [u64] = a_ref;

            a_ref2[1] = 19;

            assert(a@ === seq![0, 19, 2]);
        }

        fn fails() {
            let mut a: [u64; 3] = [0, 1, 2];
            let a_ref: &mut [u64; 3] = &mut a;
            let a_ref2: &mut [u64] = a_ref;

            a_ref2[1] = 19;

            assert(a@ === seq![0, 19, 2]);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}
