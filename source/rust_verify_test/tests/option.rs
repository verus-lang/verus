#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_unwrap_expect verus_code! {
        use vstd::prelude::*;

        struct Err {
            error_code: int,
        }

        proof fn test_option() {
            let ok_option = Option::<i8>::Some(1);
            assert(ok_option is Some);
            assert(ok_option.unwrap() == 1);
            let ok_option2 = Option::<i8>::Some(1);
            assert(ok_option2 is Some);
            assert(ok_option2.expect("option was built with Some") == 1);
            let none_option = Option::<i8>::None;
            assert(none_option is None);
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test_as_mut_spec ["new-mut-ref"] => verus_code! {
        use vstd::prelude::*;

        fn test1() {
            let mut opt = Some(5);
            let opt_ref_int = opt.as_mut();
            let ref_int = opt_ref_int.unwrap();
            *ref_int = 20;
            assert(opt === Some(20));
        }

        fn test1_fails() {
            let mut opt = Some(5);
            let opt_ref_int = opt.as_mut();
            let ref_int = opt_ref_int.unwrap();
            *ref_int = 20;
            assert(opt === Some(20));
            assert(false); // FAILS
        }

        fn test2() {
            let mut opt = None::<u64>;
            let opt_ref_int = opt.as_mut();
            assert(opt_ref_int === None);
            assert(opt === None);
        }

        fn test2_fails() {
            let mut opt = None::<u64>;
            let opt_ref_int = opt.as_mut();
            assert(opt_ref_int === None);
            assert(opt === None);
            assert(false); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
