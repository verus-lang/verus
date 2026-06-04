#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file_with_options! {
    #[test] test_basic [] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let mut a = 0;

            let b = &mut a;
            let ghost b1 = mut_ref_ptr(b);

            *b = 20;
            let ghost b2 = mut_ref_ptr(b);

            assert(b1 == b2);

            let c = &mut *b;
            let ghost c1 = mut_ref_ptr(c);

            assert(c1.addr() == b1.addr());
            assert(c1 == b1); // FAILS

            let d = &mut a;

            let ghost d1 = mut_ref_ptr(d);
            assert(d1 == b1); // FAILS
        }

        fn test_box(x: &mut Box<u64>) {
            let a: &mut u64 = &mut **x;
            assert(mut_ref_ptr(a).addr() == mut_ref_ptr(x).addr()); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}
