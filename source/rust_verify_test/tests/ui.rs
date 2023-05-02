#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] regression_114_unrelated_precondition verus_code! {
        fn get_bool() -> (b: bool)
            ensures b == true
        {
            true
        }

        fn require_false() -> bool
            requires false // INCORRECT CONTEXT
        {
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
        assert!(!e.errors[0].spans.iter().any(|x| x.text[0].text.contains("INCORRECT CONTEXT")));
    }
}
