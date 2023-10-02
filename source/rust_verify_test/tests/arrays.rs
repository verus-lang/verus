#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::array::*;

        fn test(ar: [u8; 20])
            requires ar[1] == 19
        {
            let x = array_index_get(&ar, 1);
            assert(x == 19);
        }

        fn test2(ar: [u8; 20]) {
            let y = array_index_get(&ar, 20); // FAILS
        }

        fn test3(ar: [u8; 20]) {
            assert(ar@.len() == 20);
        }

        fn test4(ar: [u8; 20]) {
            assert(ar@.len() == 21); // FAILS
        }

        fn test5<const N: usize>(ar: [u8; N]) {
            assert(ar@.len() == N);
        }

        fn test6(ar: [u8; 20]) {
            let mut ar = ar;
            ar.set(7, 50);
            assert(ar[7] == 50);
        }

        fn test7(ar: [u8; 20])
            requires ar[1] == 19
        {
            let x = ar[1];
            assert(x == 19);
        }

        fn test8(ar: [u8; 20]) {
            let y = ar[20]; // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_recursion_checks_1 verus_code! {
        use vstd::array::*;
        use vstd::map::*;

        struct Foo {
            field: [ Map<Foo, int> ; 20 ],
        }

    } => Err(err) => assert_vir_error_msg(err, "non-positive position")
}

test_verify_one_file! {
    #[test] test_recursion_checks_2 verus_code! {
        use vstd::array::*;

        struct Foo {
            field: Box<[ Foo ; 1 ]>,
        }

    } => Ok(())
}
