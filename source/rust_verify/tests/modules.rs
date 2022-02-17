#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const M1: &str = code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        #[spec]
        #[verifier(publish)]
        pub fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_adt_0 M1.to_string() + code_str! {
        mod M2 {
            use crate::M1::Car;
            use builtin::*;
            use crate::pervasive::*;

            fn mod_adt_0() {
                assert(!Car { four_doors: false }.four_doors);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_adt_1 M1.to_string() + code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use builtin::*;
            use crate::pervasive::*;

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

const M1_OPAQUE: &str = code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        #[spec]
        #[verifier(publish_opaque)]
        pub fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_no_reveal M1_OPAQUE.to_string() + code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use builtin::*;
            use crate::pervasive::*;

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c)); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_reveal M1_OPAQUE.to_string() + code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use builtin::*;
            use crate::pervasive::*;

            fn test() {
                let c = Car { four_doors: true };
                reveal(is_four_doors);
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_adt_no_verify code! {
        #[verifier(abstract_def)]
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        fn mod_adt_no_verify() {
            assert(!Car { four_doors: false }.four_doors);
        }
    } => Err(err) => assert_vir_error(err)
}
