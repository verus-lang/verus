#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] calc_basics verus_code! {
        use vstd::seq::*;
        use vstd::seq_lib::*;
        use vstd::calc_macro::*;

        proof fn foo() {
            let a: Seq<u8> = seq![1u8, 2u8];
            let b: Seq<u8> = seq![1u8];
            let c: Seq<u8> = seq![2u8];
            let d: Seq<u8> = seq![1u8, 2u8];

            calc! {
                (==)
                a; { assert_seqs_equal!(a == b + c); }
                b + c; { assert_seqs_equal!(b + c == d); }
                d;
            };

            assert(a == d);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] calc_intermediate_relations verus_code! {
        use vstd::calc_macro::*;

        proof fn foo() {
            let x: int = 2;

            calc! {
                (<=)
                (2 as int); (==) { }
                3 - 1; (<) { }
                5;
            };

            assert(x <= 5);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] calc_hides_intermediates verus_code! {
        // Calc should not be revealing any of the intermediate steps to the outside context.
        use vstd::seq::*;
        use vstd::seq_lib::*;
        use vstd::calc_macro::*;

        proof fn foo() {
            let a: Seq<u8> = seq![1u8, 2u8];
            let b: Seq<u8> = seq![123u8, 45u8];
            let c: Seq<u8> = seq![67u8, 89u8];
            let d: Seq<u8> = seq![1u8, 2u8];

            calc! {
                (==)
                a; { assume(false); } // ridiculous but we are only
                b; { assume(false); } // using these to confirm that
                c; { assume(false); } // context is not leaking outside
                d;
            };

            assert(b == d); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] calc_keeps_intermediates_distinct verus_code! {
        // Calc should not allow info to flow from one intermediate context to another.
        use vstd::seq::*;
        use vstd::seq_lib::*;
        use vstd::calc_macro::*;

        proof fn foo() {
            let a: Seq<u8> = seq![1u8, 2u8];
            let b: Seq<u8> = seq![1u8];
            let c: Seq<u8> = seq![2u8];
            let d: Seq<u8> = seq![1u8, 2u8];

            calc! {
                (==)
                a; { assume(false); } // If this is exposed to other steps, that shows that other steps are reading this
                b + c; { assert(1 == 2); } // FAILS
                d;
            };
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] calc_checks_consistency_of_intermediate_relations verus_code! {
        // Calc should produce useful errors when we use inconsistent intermediates.
        use vstd::calc_macro::*;

        proof fn foo() {
            let x: int = 2;

            calc! {
                (<=)
                (2 as int); (==) { }
                3 - 1; (>) { } // Note: `>` is not useful for `<=`, so this should fail.
                1; { }
                5;
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "inconsistent relation `>` with `<=`")
}
