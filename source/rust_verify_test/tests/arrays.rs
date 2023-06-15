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
    } => Err(err) => assert_fails(err, 1)
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
