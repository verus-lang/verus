#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] prophecy_expected_use_1 verus_code! {
        use vstd::proph::*;

        fn test_bool() {
            let ghost x: int = 1;
            let p = Prophecy::<bool>::new();
            proof {
                if p@ {
                    x = 2;
                } else {
                    x = 3;
                }
            }

            p.resolve(&true);
            assert(x == 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] prophecy_expected_use_2 verus_code! {
        use vstd::proph::*;

        #[derive(PartialEq, Eq, Structural)]
        struct S {
            a: u64,
            b: u8,
            c: bool,
        }

        fn test() {
            let p = Prophecy::<S>::new();
            p.resolve(&S{a: 1u64, b: 2u8, c: false});
            assert(p@ == S{a: 1u64, b: 2u8, c: false});
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] prophecy_expected_use_3 verus_code! {
        use vstd::proph::*;

        fn test() {
            let p = Prophecy::<bool>::new();
            p.resolve(&true);
            assert(p@ == true);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] prophecy_ghost_disallowed verus_code! {
        use vstd::proph::*;

        fn test() {
            let p = Prophecy::<Ghost<bool>>::new();
            p.resolve(&Ghost(!p.view().view()));
            assert(false);
        }
    } => Err(err) => assert_rust_error_msg(err, "trait bounds were not satisfied")
}
