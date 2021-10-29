#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] basic_while code! {
        fn test1() {
            let mut i = 0;
            while i < 10 {
                invariant([
                    i <= 10
                ]);
                i = i + 1;
            }
            assert(i == 10);
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    // TODO: support break in loops?
    #[test] #[ignore] break_test code! {
        fn test1(a: int, b: int) {
            let mut i = a;
            while i >= 1 {
                if a % i == 0 && b % i == 0 {
                    break;
                }
            }
            assert(a % i == 0);
        }
    } => Ok(())
}
