#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] spinoff_attribute verus_code! {
        mod m {
            #![verifier::loop_isolation(false)]
            mod n {
                fn test_loop() {
                    let x = 10;
                    loop {
                        assert(x == 10);
                    }
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] spinoff_attribute_fail verus_code! {
        mod m {
            #![verifier::loop_isolation(false)]
            mod n {
                #[verifier::loop_isolation(true)]
                fn test_loop() {
                    let x = 10;
                    loop {
                        assert(x == 10); // FAILS
                    }
                }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] basic_while verus_code! {
        fn test1() {
            let mut i = 0;
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while i < 10 {
                i = i + 1;
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            requires 2 <= a
        {
        }

        fn test1() {
            let mut i = 0;
            let mut x = 0;
            #[verifier::loop_isolation(false)]
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
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_variables_havoc_basic verus_code! {
        fn test(a: u64)
            requires a < 10
        {
            let mut i = a;
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while i < 20 {
                assert(a < 10);
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while i < 20 {
                i = i + 1;
                let mut j = a;
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while i < 20 {
                i = i + 1;
                let mut j = a;
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while i < 20 {
                let mut k = i;
                i = i + 1;
                #[verifier::loop_isolation(false)]
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
        use vstd::modes::*;
        fn test() {
            let ghost mut a: int = 5;
            #[verifier::loop_isolation(false)]
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
    #[test] basic_loop_fail verus_code! {
        fn test() {
            let mut a: u32 = 5;
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while a < 100
                invariant a <= 100
                decreases 100 - a
            {
                a = a + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] example_loop_break verus_code! {
        fn test() {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9
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
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9 // FAILS
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
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9
            {
                break;
            }
            assert(1 <= i <= 10); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] example_loop_break_fail4 verus_code! {
        fn test() {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9
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
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9
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
            #[verifier::loop_isolation(false)]
            loop
                invariant 0 <= i <= 9
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
            #[verifier::loop_isolation(false)]
            loop {
            }
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] loop_break_false verus_code! {
        fn test() {
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            while b {
            }
            assert(!b);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] while_b_fail verus_code! {
        fn test(b: bool) {
            #[verifier::loop_isolation(false)]
            while b {
                break;
            }
            assert(!b); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] while_b2 verus_code! {
        fn test(b: bool) {
            #[verifier::loop_isolation(false)]
            while b {
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            'x: while b {
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            'x: while b {
                #[verifier::loop_isolation(false)]
                'y: while b {
                    break 'y;
                }
            }
            assert(!b);
        }
    } => Ok(_err) => { /* TODO fix warnings? */ }
}

test_verify_one_file! {
    #[test] while_to_loop_break verus_code! {
        fn test(b: bool) {
            #[verifier::loop_isolation(false)]
            while b {
                break;
            }
            assert(!b); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_infinite2 verus_code! {
        fn test() {
            #[verifier::loop_isolation(false)]
            'x: loop {
                #[verifier::loop_isolation(false)]
                'y: loop {
                    break;
                }
            }
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] loop_infinite2y verus_code! {
        fn test() {
            #[verifier::loop_isolation(false)]
            'x: loop {
                #[verifier::loop_isolation(false)]
                'y: loop {
                    break 'y;
                }
            }
            assert(false);
        }
    } => Ok(_err) => { /* allow unreachable warnings */ }
}

test_verify_one_file! {
    #[test] loop_infinite2x verus_code! {
        fn test() {
            #[verifier::loop_isolation(false)]
            'x: loop {
                #[verifier::loop_isolation(false)]
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
            #[verifier::loop_isolation(false)]
            'x: loop
                invariant i == 0
            {
                i = i + 1;
                #[verifier::loop_isolation(false)]
                'y: loop
                    invariant i == 1
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
    } => Ok(_err) => { /* TODO fix warnings? */ }
}

test_verify_one_file! {
    #[test] loop2_ok_y verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            'x: loop
                invariant i == 0
            {
                i = i + 1;
                #[verifier::loop_isolation(false)]
                'y: loop
                    invariant i == 1
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
    } => Ok(_err) => { /* TODO fix warnings? */ }
}

test_verify_one_file! {
    #[test] loop2_fail1 verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            'x: loop
                invariant i == 0
            {
                i = i + 1;
                #[verifier::loop_isolation(false)]
                'y: loop
                    invariant i == 1
                {
                    break 'x;
                }
                i = i - 1;
                if b {
                    break;
                }
            }
            assert(i == 0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop2_fail2 verus_code! {
        fn test(b: bool) {
            let mut i: i8 = 0;
            #[verifier::loop_isolation(false)]
            'x: loop
                invariant i == 0
            {
                i = i + 1;
                #[verifier::loop_isolation(false)]
                'y: loop
                    invariant i == 1
                {
                    break;
                }
                if b {
                    break;
                }
                i = i - 1;
            }
            assert(i == 0); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_decreases1 verus_code! {
        #[verifier::loop_isolation(false)]
        fn test1() {
            let mut i: u8 = 100;
            loop
                decreases i
            {
                if i == 0 {
                    break;
                }
                if i == 20 {
                    continue; // FAILS
                }
                i = i - 1;
            }
        }

        #[verifier::loop_isolation(false)]
        fn test2() {
            let mut i: u8 = 100;
            loop  // FAILS
                decreases i
            {
                if i == 0 {
                    break;
                }
                if i == 20 {
                    i = i - 1;
                    continue;
                }
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] loop_decreases2 verus_code! {
        #[verifier::loop_isolation(false)]
        fn test1() {
            let mut i: u8 = 100;
            let mut j: u8 = 100;
            while i > 0
                decreases i
            {
                while j > 0
                    decreases j
                {
                    j = j - 1;
                }
                i = i - 1;
            }
        }

        #[verifier::loop_isolation(false)]
        fn test2() {
            let mut i: u8 = 100;
            let mut j: u8 = 100;
            while i > 0
                decreases i
            {
                while j > 0 // FAILS
                    decreases j
                {
                }
                i = i - 1;
            }
        }

        #[verifier::loop_isolation(false)]
        fn test3() {
            let mut i: u8 = 100;
            let mut j: u8 = 100;
            while i > 0 // FAILS
                decreases i
            {
                while j > 0
                    decreases j
                {
                    j = j - 1;
                }
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] loop_decreases3 verus_code! {
        #[verifier::loop_isolation(false)]
        fn test_c() {
            'a: loop
                decreases 3u8
            {
                loop
                {
                    continue 'a; // FAILS
                }
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] loop_references_old_version_of_mut_var verus_code! {
        fn foo(a: &mut u64)
            requires *old(a) === 17
        {
            *a = 19;
            #[verifier::loop_isolation(false)]
            loop
                invariant
                    *old(a) === 17,
                    *a === 19,
            {
                assert(false); // FAILS
            }
        }

        fn foo2(a: &mut u64) {
            #[verifier::loop_isolation(false)]
            loop
                invariant *old(a) === *a,
            {
            }
        }


        fn foo3(a: &mut u64)
            requires *old(a) === 1234,
        {
            #[verifier::loop_isolation(false)]
            loop
                invariant *old(a) === 1234,
            {
            }
        }

        fn foo4(a: &mut u64)
            requires *old(a) === 1234,
        {
            #[verifier::loop_isolation(false)]
            loop
                invariant *old(a) === 1234,
            {
                *a = 8932759;
            }
        }

        fn foo5(a: &mut u64)
            requires *old(a) === 1234,
        {
            *a = 12;
            #[verifier::loop_isolation(false)]
            loop
                invariant *a === 12,
            {
                assert(*a === 12);
            }
        }

        fn test_old_in_ensures(a: &mut u64)
            requires *old(a) < 2000,
            ensures *a as int === *old(a) + 25,
        {
            let mut i: u64 = 0;
            #[verifier::loop_isolation(false)]
            loop
                invariant
                    0 <= i < 25,
                    *a as int === *old(a) + i,
            {
                *a = *a + 1;
                i = i + 1;
                if i == 25 {
                    return;
                }
            }
        }

        fn test_old_in_ensures_fail(a: &mut u64)
            requires *old(a) < 2000,
            ensures *a as int === *old(a) + 26,
        {
            let mut i: u64 = 0;
            #[verifier::loop_isolation(false)]
            loop
                invariant *old(a) < 2000,
                    0 <= i < 25,
                    *a as int === *old(a) + i,
            {
                *a = *a + 1;
                i = i + 1;
                if i == 25 {
                    return; // FAILS
                }
            }
        }
    } => Err(e) => assert_fails(e, 2)
}

test_verify_one_file! {
    #[test] boxed_args_are_havoced_regression_340 verus_code! {
        use vstd::prelude::*;

        mod Mod {
            pub struct X<T> {
                t: T, // private
            }

            impl<T> X<T> {
                pub closed spec fn view(&self) -> T { self.t }

                pub fn new(t: T) -> (s: Self)
                  ensures s.view() === t
                {
                    X { t: t }
                }

                pub fn some_mutator(&mut self) {
                }
            }

            pub fn some_mutator<T>(x: &mut X<T>) {
            }
        }

        fn test1() {
            let mut x = Mod::X::<u64>::new(5);
            assert(x.view() == 5);

            let mut i = 0;

            #[verifier::loop_isolation(false)]
            while i < 5 {
                x.some_mutator();
                i = i + 1;
            }

            assert(x.view() == 5); // FAILS
        }

        fn test2() {
            let mut x = Mod::X::<u64>::new(5);
            assert(x.view() == 5);

            let mut i = 0;

            #[verifier::loop_isolation(false)]
            while i < 5 {
                Mod::some_mutator(&mut x);
                i = i + 1;
            }

            assert(x.view() == 5); // FAILS
        }

        fn test3() {
            let mut v = Vec::<u64>::new();

            let mut i = 0;
            #[verifier::loop_isolation(false)]
            while i < 5
                invariant
                    v.view().len() == i as int
            {
                v.push(7);
                i = i + 1;
            }

            assert(v.view().len() == 0); // FAILS
        }
    } => Err(e) => assert_fails(e, 3)
}

test_verify_one_file! {
    #[test] iter_loop verus_code! {
        use vstd::prelude::*;
        fn test_loop() {
            let mut n: u64 = 0;
            let mut iter = (0..10).into_iter();
            #[verifier::loop_isolation(false)]
            loop
                invariant
                    iter.start <= 10,
                    iter.end == 10,
                    n == iter.start * 3,
            {
                if let Some(x) = iter.next() {
                    assert(x < 10);
                    assert(x == iter.start - 1);
                    n += 3;
                } else {
                    break;
                }
            }
            assert(iter.start == 10);
            assert(n == 30);
        }

        fn test_loop_fail() {
            let mut n: u64 = 0;
            let mut iter = (0..10).into_iter();
            #[verifier::loop_isolation(false)]
            loop
                invariant
                    iter.start <= 10,
                    iter.end == 10,
                    n == iter.start * 3,
            {
                if let Some(x) = iter.next() {
                    assert(x < 9); // FAILS
                    assert(x == iter.start - 1);
                    n += 3;
                } else {
                    break;
                }
            }
            assert(iter.start == 10);
            assert(n == 30);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] for_loop1 verus_code! {
        use vstd::prelude::*;
        fn test_loop() {
            let mut n: u64 = 0;
            #[verifier::loop_isolation(false)]
            for x in iter: 0..10
                invariant n == iter.cur * 3,
            {
                assert(x < 10);
                assert(x == iter.cur);
                n += 3;
            }
            assert(n == 30);
        }

        fn test_loop_peek() {
            let mut n: u64 = 0;
            #[verifier::loop_isolation(false)]
            for x in 0..10
                invariant n == x * 3,
            {
                assert(x < 10);
                n += 3;
            }
            assert(n == 30);
        }

        fn test_loop_fail() {
            let mut n: u64 = 0;
            #[verifier::loop_isolation(false)]
            for x in iter: 0..10
                invariant n == iter.cur * 3,
            {
                assert(x < 9); // FAILS
                assert(x == iter.cur);
                n += 3;
            }
            assert(n == 30);
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] for_loop2 verus_code! {
        use vstd::prelude::*;
        fn test_loop() {
            let mut n: u64 = 0;
            let mut end = 10;
            #[verifier::loop_isolation(false)]
            for x in iter: 0..end
                invariant
                    n == iter.cur * 3,
                    end == 10,
            {
                assert(x < 10);
                assert(x == iter.cur);
                n += 3;
            }
            assert(n == 30);
        }

        fn test_loop_fail() {
            let mut n: u64 = 0;
            let mut end = 10;
            #[verifier::loop_isolation(false)]
            for x in iter: 0..end
                invariant
                    n == iter.cur * 3,
                    end == 10,
            {
                assert(x < 10); // FAILS
                assert(x == iter.cur);
                n += 3;
                end = end + 0; // causes end to be non-constant, so loop needs more invariants
            }
        }

        fn non_spec() {}

        fn test_loop_modes_transient_state() {
            let mut n: u64 = 0;
            let mut end = 10;
            // test Typing::snapshot_transient_state
            #[verifier::loop_isolation(false)]
            for x in iter: 0..({let z = end; non_spec(); z})
                invariant
                    n == iter.cur * 3,
                    end == 10,
            {
                n += 3;
                end = end + 0; // causes end to be non-constant
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] for_loop3 verus_code! {
        use vstd::prelude::*;
        fn test_loop(n: u32) -> (v: Vec<u32>)
            ensures
                v.len() == n,
                forall|i: int| 0 <= i < n ==> v[i] == i,
        {
            let mut v: Vec<u32> = Vec::new();
            #[verifier::loop_isolation(false)]
            for i in iter: 0..n
                invariant
                    v@ =~= iter@,
            {
                v.push(i);
            }
            v
        }

        fn test_loop_fail(n: u32) -> (v: Vec<u32>)
            ensures
                v.len() == n,
                forall|i: int| 0 <= i < n ==> v[i] == i,
        {
            let mut v: Vec<u32> = Vec::new();
            #[verifier::loop_isolation(false)]
            for i in iter: 0..n
                invariant
                    v@ =~= iter@, // FAILS
            {
                v.push(0);
            }
            v
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] for_loop_vec_custom_iterator verus_code! {
        use vstd::prelude::*;

        #[verifier::external_body]
        pub closed spec fn spec_phantom_data<V: ?Sized>() -> core::marker::PhantomData<V> {
            core::marker::PhantomData::default()
        }

        pub struct VecIterCopy<'a, T: 'a> {
            pub vec: &'a Vec<T>,
            pub cur: usize,
        }

        impl<'a, T: Copy> Iterator for VecIterCopy<'a, T> {
            type Item = T;
            fn next(&mut self) -> (item: Option<T>)
                ensures
                    self.vec == old(self).vec,
                    old(self).cur < self.vec.len() ==> self.cur == old(self).cur + 1,
                    old(self).cur < self.vec.len() ==> item == Some(self.vec[old(self).cur as int]),
                    old(self).cur >= self.vec.len() ==> item.is_none() && self.cur == old(self).cur,
            {
                if self.cur < self.vec.len() {
                    let item = self.vec[self.cur];
                    self.cur = self.cur + 1;
                    Some(item)
                } else {
                    None
                }
            }
        }

        pub struct VecGhostIterCopy<'a, T> {
            pub seq: Seq<T>,
            pub cur: int,
            pub phantom: core::marker::PhantomData<&'a T>,
        }

        impl<'a, T: 'a> vstd::pervasive::ForLoopGhostIteratorNew for VecIterCopy<'a, T> {
            type GhostIter = VecGhostIterCopy<'a, T>;

            open spec fn ghost_iter(&self) -> VecGhostIterCopy<'a, T> {
                VecGhostIterCopy {
                    seq: self.vec@,
                    cur: 0,
                    phantom: spec_phantom_data(),
                }
            }
        }

        impl<'a, T: 'a> vstd::pervasive::ForLoopGhostIterator for VecGhostIterCopy<'a, T> {
            type ExecIter = VecIterCopy<'a, T>;
            type Item = T;
            type Decrease = int;

            open spec fn exec_invariant(&self, exec_iter: &VecIterCopy<'a, T>) -> bool {
                &&& self.seq == exec_iter.vec@
                &&& self.cur == exec_iter.cur
            }

            open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
                &&& 0 <= self.cur <= self.seq.len()
                &&& if let Some(init) = init {
                        init.seq == self.seq
                    } else {
                        true
                    }
            }

            open spec fn ghost_ensures(&self) -> bool {
                self.cur >= self.seq.len()
            }

            open spec fn ghost_decrease(&self) -> Option<int> {
                Some(self.seq.len() - self.cur)
            }

            open spec fn ghost_peek_next(&self) -> Option<T> {
                if 0 <= self.cur < self.seq.len() {
                    Some(self.seq[self.cur])
                } else {
                    None
                }
            }

            open spec fn ghost_advance(&self, _exec_iter: &VecIterCopy<T>) -> VecGhostIterCopy<'a, T> {
                VecGhostIterCopy { cur: self.cur + 1, ..*self }
            }
        }

        impl<'a, T: 'a> vstd::view::View for VecGhostIterCopy<'a, T> {
            type V = Seq<T>;

            open spec fn view(&self) -> Seq<T> {
                self.seq.subrange(0, self.cur)
            }
        }

        spec fn vec_iter_copy_spec<'a, T: 'a>(vec: &'a Vec<T>) -> VecIterCopy<'a, T> {
            VecIterCopy { vec, cur: 0 }
        }

        #[verifier::when_used_as_spec(vec_iter_copy_spec)]
        fn vec_iter_copy<'a, T: 'a>(vec: &'a Vec<T>) -> (iter: VecIterCopy<'a, T>)
            ensures
                iter == (VecIterCopy { vec, cur: 0 }),
        {
            VecIterCopy { vec, cur: 0 }
        }

        fn all_positive(v: &Vec<u8>) -> (b: bool)
            ensures
                b <==> (forall|i: int| 0 <= i < v.len() ==> v[i] > 0),
        {
            let mut b: bool = true;

            #[verifier::loop_isolation(false)]
            for x in iter: vec_iter_copy(v)
                invariant
                    b <==> (forall|i: int| 0 <= i < iter.cur ==> v[i] > 0),
            {
                b = b && x > 0;
            }
            b
        }
    } => Ok(())
}
