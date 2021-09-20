#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const STRUCT: &str = code_str! {
    #[derive(PartialEq, Eq)]
    struct Bike {
        hard_tail: bool,
    }
};

test_verify_with_pervasive! {
    #[test] test_impl_1 STRUCT.to_string() + code_str! {
        impl Bike {
            #[spec]
            pub fn is_hard_tail(&self) -> bool {
                self.hard_tail
            }
        }

        fn test_impl_1(b: Bike) {
            requires(b.is_hard_tail());
            assert(b.hard_tail);
        }

    } => Ok(())
}
