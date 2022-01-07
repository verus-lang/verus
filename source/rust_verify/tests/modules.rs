#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_mod_adt_0 code! {
        mod M1 {
            #[derive(PartialEq, Eq)]
            pub struct Car {
                pub four_doors: bool,
            }

            #[spec]
            pub fn is_four_doors(c: Car) -> bool {
                c.four_doors
            }
        }

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
    #[test] test_mod_adt_no_verify code! {
        #[verifier(external_body)]
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        fn mod_adt_no_verify() {
            assert(!Car { four_doors: false }.four_doors);
        }
    } => Err(err) => assert_vir_error(err)
}
