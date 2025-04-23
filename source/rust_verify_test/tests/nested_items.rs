#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_ignorable_items verus_code! {
        mod m {
            // Verus can ignore 'use' item
            use super::*;

            pub open spec fn test() -> bool { true }
        }

        fn test_use_item() {
            use m::test as test2;
            assert(test2());
        }

        fn test_macro_item() {
            let mut x = 1;

            // Verus can ignore 'macro' item
            macro_rules! add_1 {
                () => {
                    x = x + 1;
                }
            }

            add_1!();

            assert(x == 2);
        }
    } => Ok(())
}
