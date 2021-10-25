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

        fn test_impl_2(b: &Bike) {
            requires(b.is_hard_tail());
            assert(b.hard_tail);
        }

    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test_impl_mod_1 code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Bike {
                pub hard_tail: bool,
            }

            impl Bike {
                #[spec]
                pub fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }
            }
        }

        mod M2 {
            use super::M1::Bike;
            use builtin::*;
            use crate::pervasive::*;

            fn test_impl_1(b: Bike) {
                requires(b.is_hard_tail());
                assert(b.is_hard_tail());
            }
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test_impl_mod_priv_field code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Bike {
                hard_tail: bool,
            }

            impl Bike {
                #[spec]
                #[verifier(pub_abstract)]
                pub fn is_hard_tail(&self) -> bool {
                    self.hard_tail
                }
            }
        }

        mod M2 {
            use super::M1::Bike;
            use builtin::*;
            use crate::pervasive::*;

            fn test_impl_1(b: Bike) {
                requires(b.is_hard_tail());
                assert(b.is_hard_tail());
            }
        }
    } => Ok(())
}
