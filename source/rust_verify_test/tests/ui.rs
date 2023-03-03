#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[ignore] #[test] regression_114_unrelated_precondition code! {
        fn get_bool() -> bool {
            ensures(|b: bool| b == true);
            true
        }

        fn require_false() -> bool {
            requires(false); // INCORRECT CONTEXT
            false
        }

        fn test() {
            let x = 6;

            if !get_bool() {
                require_false();
            }

            assert(x == 7); // FAILS
        }
    } => Err(e) => {
        assert!(e.errors.len() == 1);
        assert!(!e.errors[0].iter().any(|x| x.test_span_line.contains("INCORRECT CONTEXT")));
    }
}
