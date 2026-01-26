#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_implies verus_code! {
        fn test_implies (u : i8) {
            assert(u < 100 ==> true) by (compute);
        }

        fn main() {
            test_implies(98);
            return
        }
    } => Ok(())
}