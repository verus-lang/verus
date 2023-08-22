#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_needs_pub_abstract verus_code! {
        mod M1 {
            use builtin::*;

            #[derive(PartialEq, Eq)]
            pub struct Car {
                passengers: nat,
                pub four_doors: bool,
            }

            pub open spec fn get_passengers(c: Car) -> nat {
                c.passengers
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot access any field of a datatype where one or more fields are private")
}

test_verify_one_file! {
    #[test] test_needs_pub_abstract2 verus_code! {
        mod M1 {
            use builtin::*;

            #[derive(PartialEq, Eq)]
            pub struct Car {
                passengers: nat,
                pub four_doors: bool,
            }

            pub open spec fn get_passengers() -> Car {
                Car { passengers: 0, four_doors: true }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot use constructor of private datatype or datatype whose fields are private")
}

test_verify_one_file! {
    #[test] test_needs_pub_abstract3 verus_code! {
        mod M1 {
            use builtin::*;

            enum E {
                C()
            }

            pub open spec fn get_passengers() -> bool {
                let _ = E::C();
                true
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot use constructor of private datatype or datatype whose fields are private")
}

const M1: &str = verus_code_str! {
    mod M1 {
        use builtin::*;

        #[derive(PartialEq, Eq)]
        pub struct Car {
            passengers: nat,
            pub four_doors: bool,
        }

        pub closed spec fn get_passengers(c: Car) -> nat {
            c.passengers
        }

        #[derive(PartialEq, Eq)]
        pub struct Bike {
            pub hard_tail: bool,
        }
    }
};

test_verify_one_file! {
    #[test] test_transparent_struct_1 M1.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{Car, Bike};
            use builtin::*;

            fn test_transparent_struct_1() {
                assert((Bike { hard_tail: true }).hard_tail);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_struct_1 M1.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{Car, get_passengers, Bike};
            use builtin::*;

            fn test_opaque_struct_1(c: Car)
                requires
                    get_passengers(c) == 12,
            {
                assert(get_passengers(c) == 12);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_fn verus_code! {
        struct A {}

        impl A {
            #[verifier(opaque)] /* vattr */
            pub closed spec fn always(&self) -> bool {
                true
            }
        }

        fn main() {
            let a = A {};
            proof {
                reveal(A::always);
            }
            assert(a.always());
        }
    } => Ok(())
}

const M1_OPAQUE: &str = verus_code_str! {
    mod M1 {
        use builtin::*;

        pub struct A {
            field: u64,
        }

        impl A {
            #[verifier(opaque_outside_module)] /* vattr */
            pub open spec fn always(&self) -> bool {
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
    #[test] test_opaque_fn_modules_pass M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use builtin::*;

            fn test(a: crate::M1::A) {
                proof {
                    reveal(crate::M1::A::always);
                }
                assert(a.always());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_fn_modules_fail M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use builtin::*;

            fn test(a: crate::M1::A) {
                assert(a.always()); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}
