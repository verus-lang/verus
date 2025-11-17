#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_externals_available_without_declaration1 verus_code! {
        #[verifier::external]
        fn f0() {}

        #[verifier::external]
        fn f1() -> u8 { 3 }

        #[verifier::external]
        fn f2(u: &mut u8) -> u8 { 3 }

        #[verifier::external]
        fn f3(u: u8) {}

        assume_specification[ f3 ](u: u8)
            requires
                u > 10,
        ;

        #[verifier::assume(externals_available_without_declaration)]
        fn g0() {
            f0();
            f3(5); // FAILS
        }

        #[verifier::assume(externals_available_without_declaration)]
        mod m {
            fn g0() {
                super::f0();
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::assume(externals_available_without_declaration)]
        fn g1() {
            let mut x = 3;
            x = f1();
            assert(x >= 0);
            assert(x == 3); // FAILS
            loop {
                assert(x >= 0);
                break;
            }
        }

        #[verifier::exec_allows_no_decreases_clause]
        #[verifier::assume(externals_available_without_declaration)]
        fn g2() {
            let mut x = 3;
            let u = f2(&mut x);
            assert(x >= 0);
            assert(u >= 0);
            assert(x == 3); // FAILS
            loop {
                assert(x >= 0);
                assert(u >= 0);
                break;
            }
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] test_externals_available_without_declaration2 verus_code! {
        #[verifier::external]
        fn f0() {}

        #[verifier::assume(externals_available_without_declaration)]
        mod m {
            #[verifier::deny(externals_available_without_declaration)]
            fn g0() {
                super::f0();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use function")
}
