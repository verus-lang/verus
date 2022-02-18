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
            #[verifier(publish)] // illegal
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
}

test_verify_one_file! {
    #[test] test_opaque_fn code! {
        struct A {}

        impl A {
            #[spec] #[verifier(opaque)]
            pub fn always(&self) -> bool {
                true
            }
        }

        fn main() {
            let a = A {};
            reveal(A::always);
            assert(a.always());
        }
    } => Ok(())
}

const M1_OPAQUE: &str = code_str! {
    mod M1 {
        use builtin::*;
        use crate::pervasive::*;

        pub struct A {
            field: u64,
        }

        impl A {
            #[spec] #[verifier(publish)] #[verifier(opaque_outside_module)]
            pub fn always(&self) -> bool {
                true
            }
        }

        fn test1() {
            let a = A { field: 12 };
            assert(a.always());
        }
    }
};

test_verify_one_file! {
    #[test] test_opaque_fn_modules_within M1_OPAQUE.to_string() => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_fn_modules_pass M1_OPAQUE.to_string() + code_str! {
        mod M2 {
            use builtin::*;
            use crate::pervasive::*;

            fn test(a: crate::M1::A) {
                reveal(crate::M1::A::always);
                assert(a.always());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_fn_modules_fail M1_OPAQUE.to_string() + code_str! {
        mod M2 {
            use builtin::*;
            use crate::pervasive::*;

            fn test(a: crate::M1::A) {
                assert(a.always()); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}
