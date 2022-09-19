#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_189a verus_code! {
        use set::*;

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);
            let s2: Set<i32> = Set::empty();
            assert(!s2.contains(1));
            // assert(!s1.ext_equal(s2));
            assert(s1 !== s2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_189b verus_code! {
        use set::*;

        spec fn different_set<V>(s: Set<V>) -> Set<V> { s }

        proof fn test_sets_1() {
            let s1: Set<i32> = Set::empty().insert(1);

            assert (exists|s3: Set<i32>| different_set(s3) !== s1) by {
                assert(!different_set(Set::empty()).contains(1i32));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_verifier_truncate_allowed_on_cast verus_code! {
        fn test(a: u64) -> u8 {
            #[verifier(truncate)] (a as u8)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_hygienic_identifiers_regression_279 verus_code! {
        macro_rules! assert_with_binding {
            ($s1:expr) => {
                let s1 = $s1;
                assert(s1);
            }
        }

        proof fn test() {
            let s1: nat = 0;
            assert_with_binding!(true);
            assert(s1 === 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[ignore] #[test] test_bad_span_for_postcondition_failure_regression_281 verus_code! {
        #[is_variant]
        enum Enum {
            A,
            B,
        }


        fn test(a: u32) -> (res: Enum)
            ensures (match res {
                Enum::A => a <= 10,
                Enum::B => a > 10, // FAILS
            }) {

            Enum::B
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] fields_from_macros_not_treated_as_distinct_identifiers verus_code! {
        struct Foo(pub u64);

        // Internally, the use of .0 in the macro creates an identifier `0`
        // with some extra info that is used for macro hygeine purposes.
        // However, that info needs to be ignored: the field access .0
        // should be treated like any other .0 access.

        macro_rules! some_macro {
            ($foo:ident) => {
                assert($foo.0 == 20);
            }
        }

        proof fn some_func() {
            let foo = Foo(20);
            assert(foo.0 == 20);

            some_macro!(foo);
        }

        struct Bar { val: u64 }

        macro_rules! some_macro2 {
            ($bar:ident) => {
                assert($bar.val == 30);
            }
        }

        proof fn some_func2() {
            let bar = Bar { val: 30 };
            assert(bar.val == 30);

            some_macro2!(bar);

        }
    } => Ok(())
}
