#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] #[ignore] nlarith1 code! {
        // TODO: support non-linear arithmetic?
        fn test(x: nat, y: nat, z: nat) {
            assume(x * y == z);
            assert(z % x == 0);
        }
    } => Ok(())
}
