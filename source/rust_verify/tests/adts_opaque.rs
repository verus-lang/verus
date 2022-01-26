#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_needs_pub_abstract code! {
        mod M1 {
            use builtin::*;

            #[derive(PartialEq, Eq)]
            pub struct Car {
                passengers: nat,
                pub four_doors: bool,
            }

            #[spec]
            //must have this: #[verifier(pub_abstract)]
            pub fn get_passengers(c: Car) -> nat {
                c.passengers
            }
        }
    } => Err(TestErr { has_vir_error: true, .. })
}

const M1: &str = code_str! {
    mod M1 {
        use builtin::*;

        #[derive(PartialEq, Eq)]
        pub struct Car {
            passengers: nat,
            pub four_doors: bool,
        }

        #[spec]
        #[verifier(pub_abstract)]
        pub fn get_passengers(c: Car) -> nat {
            c.passengers
        }

        #[derive(PartialEq, Eq)]
        pub struct Bike {
            pub hard_tail: bool,
        }
    }
};

test_verify_one_file! {
    #[test] test_transparent_struct_1 M1.to_string() + code_str! {
        mod M2 {
            use crate::M1::{Car, Bike};
            use builtin::*;
            use crate::pervasive::*;

            fn test_transparent_struct_1() {
                assert((Bike { hard_tail: true }).hard_tail);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_struct_1 M1.to_string() + code_str! {
        mod M2 {
            use crate::M1::{Car, get_passengers, Bike};
            use builtin::*;
            use crate::pervasive::*;

            fn test_opaque_struct_1(c: Car) {
                requires(get_passengers(c) == 12);
                assert(get_passengers(c) == 12);
            }
        }
    } => Ok(())
    // => Err(err) => assert_one_fails(err)
}
