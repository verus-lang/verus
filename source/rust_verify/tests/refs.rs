#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ref_0 code! {
        fn test_ref_0(p: int) {
            requires(p == 12);
            let b: &int = &p;
            assert(*b == 12);
        }
    } => Ok(())
}
