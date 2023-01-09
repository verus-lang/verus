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
    #[test] loop_references_old_version_of_mut_var verus_code! {
        fn foo(a: &mut u64)
            requires *old(a) === 17
        {
            *a = 19;
            loop
                invariant
                    *old(a) === 17,
                    *a === 19,
            {
                assert(false); // FAILS
            }
        }

        fn foo2(a: &mut u64) {
            loop
                invariant *old(a) === *a,
            {
            }
        }


        fn foo3(a: &mut u64)
            requires *old(a) === 1234,
        {
            loop
                invariant *old(a) === 1234,
            {
            }
        }

        fn foo4(a: &mut u64)
            requires *old(a) === 1234,
        {
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
            loop
                invariant *old(a) < 2000,
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
        use pervasive::vec::*;

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

            while i < 5 {
                Mod::some_mutator(&mut x);
                i = i + 1;
            }

            assert(x.view() == 5); // FAILS
        }

        fn test3() {
            let mut v = Vec::<u64>::new();

            let mut i = 0;
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
