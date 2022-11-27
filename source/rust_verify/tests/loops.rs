#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic_while verus_code! {
        fn test1() {
            let mut i = 0;
            while i < 10
                invariant i <= 10
            {
                i = i + 1;
            }
            assert(i == 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_while_fail1 verus_code! {
        fn test1() {
            let mut i = 0;
            while i < 10 {
                i = i + 1;
            }
            assert(i == 10); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_while_fail2 verus_code! {
        fn test1() {
            let mut i = 0;
            let mut j = 0;
            while i < 10 {
                i = i + 1;
                while j < 5 {
                    j = j + 1;
                }
            }
            assert(j == 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] complex_while verus_code! {
        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {x = x + 1; i < 10}
                invariant
                    i <= 10,
                    x == i,
            {
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] complex_while_fail1 verus_code! {
        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {x = x + 1; i < 10}
                invariant
                    i <= 10,
                    x == i,
            {
                i = i + 1;
            }
            assert(i == 10);
            assert(x != 11); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] complex_while2 verus_code! {
        proof fn check(a: u64)
            requires 1 <= a
        {
        }

        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {
                x = x + 1;
                proof { check(x); }
                i < 10
            }
                invariant
                    i <= 10,
                    x == i,
            {
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] complex_while2_fail verus_code! {
        proof fn check(a: u64)
            requires 2 <= a // FAILS
        {
        }

        fn test1() {
            let mut i = 0;
            let mut x = 0;
            while {
                x = x + 1;
                proof { check(x); } // FAILS
                i < 10
            }
                invariant
                    i <= 10,
                    x == i,
            {
                i = i + 1;
            }
            assert(i == 10);
            assert(x == 11);
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    // TODO: support break in loops
    #[test] #[ignore] break_test verus_code! {
        fn test1(a: int, b: int) {
            let mut i = a;
            loop {
                if a % i == 0 && b % i == 0 {
                    break;
                }
            }
            assert(a % i == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_havoc_basic verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            while i < 20 {
                i = i + 1;
            }
            assert(i == a); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_variables_not_havoc_basic verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            let mut j = a;
            j = j + 2;
            while i < 20 {
                i = i + 1;
            }
            j = j + 2;
            assert(j == a + 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_no_effect_basic verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            let mut k = 12;
            while i < 20 {
                let mut k = i;
                i = i + 1;
                k = k + 1;
                assert(k == i);
            }
            k = k + 1;
            assert(k == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_havoc_nested verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            while i < 20 {
                i = i + 1;
                let mut j = a;
                while j < 10 {
                    j = j + 1;
                }
                assert(j == a); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_variables_not_havoc_nested verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            let mut j = a;
            j = j + 2;
            while i < 20 {
                i = i + 1;
                let mut j = a;
                while j < 20 {
                    j = j + 1;
                }
            }
            j = j + 2;
            assert(j == a + 4);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_variables_no_effect_nested verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            let mut k = 12;
            while i < 20 {
                let mut k = i;
                i = i + 1;
                while k < 20 {
                    k = k + 1;
                }
            }
            k = k + 1;
            assert(k == 13);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_loop verus_code! {
        use pervasive::modes::*;
        fn test() {
            let mut a: Ghost<int> = ghost(5);
            loop
                invariant a@ > 0
            {
                proof {
                    a@ = a@ + 1;
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] basic_loop_fail verus_code! {
        fn test() {
            let mut a: u32 = 5;
            loop
                invariant a > 0 // FAILS
            {
                a = a - 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_loop_new_vars verus_code! {
        fn test() {
            let mut a: u32 = 5;
            while a < 100
                invariant
                    ({let b: int = 0; a > b}),
                    ({let b: int = 0; a > b}),
            {
                a = a + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] regression_11_incorrect_loop_header verus_code! {
        fn test() {
            let mut a: u64 = 0;
            while a < 100
                invariant a <= 100
            {
                requires(a <= 100);
                a = a + 1;
            }
        }
    } => Err(e) => assert_vir_error(e)
}

const MUT_REF_COMMON: &str = verus_code_str! {
    fn update_x(x: &mut bool) {
        *x = false;
    }
};

test_verify_one_file! {
    #[test] mut_ref_havoc_loop_1_regression_231 MUT_REF_COMMON.to_string() + verus_code_str! {
        fn foo(x: &mut bool)
            requires *old(x) == true
        {
            assert(*x == true);

            let mut i = 0;
            while i < 5 {
                i = i + 1;

                update_x(x);
            }

            assert(*x == true); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] mut_ref_havoc_loop_2_regression_231 MUT_REF_COMMON.to_string() + verus_code_str! {
        fn foo2() {
            let mut x = true;

            let mut i = 0;
            while i < 5 {
                i = i + 1;

                update_x(&mut x);
            }

            assert(x == true); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_termination_unsupported verus_code! {
        fn test() {
            let mut a: u64 = 0;
            while a < 100
                invariant a <= 100
                decreases 100 - a
            {
                a = a + 1;
            }
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] example_loop_break verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] example_loop_break_fail1 verus_code! {
        fn test() {
            let mut i: i8 = 10;
            loop
                invariant i <= 9 // FAILS
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] example_loop_break_fail2 verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 8 // FAILS
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] example_loop_break_fail3 verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                break; // FAILS
            }
            assert(1 <= i <= 10);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] example_loop_break_fail4 verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    break;
                }
            }
            assert(i <= 9); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] example_loop_continue verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 5 {
                    continue;
                }
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] example_loop_continue_fail verus_code! {
        fn test() {
            let mut i: i8 = 0;
            loop
                invariant i <= 9
                invariant_ensures 0 <= i <= 10
                ensures 1 <= i
            {
                assert(i <= 9);
                i = i + 1;
                if i == 10 {
                    continue; // FAILS
                }
                if i == 10 {
                    break;
                }
            }
            assert(1 <= i <= 10);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] infinite_loop verus_code! {
        fn test() {
            loop {
            }
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_break_false verus_code! {
        fn test() {
            loop {
                break;
            }
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_break_false_y verus_code! {
        fn test() {
            'y: loop {
                break;
            }
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] while_b verus_code! {
        fn test(b: bool) {
            while b {
            }
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] while_b_ok verus_code! {
        fn test(b: bool) {
            while b
                ensures !b
            {
            }
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] while_b_fail verus_code! {
        fn test(b: bool) {
            while b
                ensures !b
            {
                break; // FAILS
            }
            assert(!b);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] while_b2 verus_code! {
        fn test(b: bool) {
            while b {
                while b {
                    break;
                }
            }
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] while_b2_x verus_code! {
        fn test(b: bool) {
            'x: while b {
                'y: while b {
                    break 'x;
                }
            }
            assert(!b); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] while_b2_y verus_code! {
        fn test(b: bool) {
            'x: while b {
                'y: while b {
                    break 'y;
                }
            }
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] while_to_loop_ensures verus_code! {
        fn test(b: bool) {
            while b
                ensures true
            {
            }
            assert(!b); // FAILS (while converted to loop due to ensures)
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] while_to_loop_break verus_code! {
        fn test(b: bool) {
            while b {
                break;
            }
            assert(!b); // FAILS (while converted to loop due to break)
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_infinite2 verus_code! {
        fn test() {
            'x: loop {
                'y: loop {
                    break;
                }
            }
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_infinite2y verus_code! {
        fn test() {
            'x: loop {
                'y: loop {
                    break 'y;
                }
            }
            assert(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop_infinite2x verus_code! {
        fn test() {
            'x: loop {
                'y: loop {
                    break 'x;
                }
            }
            assert(false); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop2_ok verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            'x: loop
                invariant_ensures i == 0
            {
                i = i + 1;
                'y: loop
                    invariant_ensures i == 1
                {
                    break;
                }
                i = i - 1;
                if b {
                    break;
                }
            }
            assert(i == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop2_ok_y verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            'x: loop
                invariant_ensures i == 0
            {
                i = i + 1;
                'y: loop
                    invariant_ensures i == 1
                {
                    break 'y;
                }
                i = i - 1;
                if b {
                    break;
                }
            }
            assert(i == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] loop2_fail1 verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            'x: loop
                invariant_ensures i == 0
            {
                i = i + 1;
                'y: loop
                    invariant_ensures i == 1
                {
                    break 'x; // FAILS
                }
                i = i - 1;
                if b {
                    break;
                }
            }
            assert(i == 0);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop2_fail2 verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            'x: loop
                invariant_ensures i == 0
            {
                i = i + 1;
                'y: loop
                    invariant_ensures i == 1
                {
                    break;
                }
                if b {
                    break; // FAILS
                }
                i = i - 1;
            }
            assert(i == 0);
        }
    } => Err(e) => assert_one_fails(e)
}
