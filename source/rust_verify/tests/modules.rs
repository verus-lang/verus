#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const M1: &str = verus_code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        pub open spec fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_adt_0 M1.to_string() + verus_code_str! {
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
    #[test] test_mod_adt_1 M1.to_string() + verus_code_str! {
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

        #[verifier::spec]
        #[verifier(publish)] /* vattr */ #[verifier(opaque_outside_module)] /* vattr */
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
        #[verifier(external_body)] /* vattr */
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        fn mod_adt_no_verify() {
            assert(!Car { four_doors: false }.four_doors);
        }
    } => Err(err) => assert_vir_error_msg(err, "field access of datatype with inaccessible fields")
}

test_verify_one_file! {
    #[test] test_mod_child_ok code! {
        #[verifier::spec]
        fn f() -> bool {
            true
        }

        mod M1 {
            fn test() {
                builtin::ensures(crate::f());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_sibling_fail code! {
        mod M0 {
            #[verifier::spec]
            pub fn f() -> bool {
                true
            }
        }

        mod M1 {
            fn test() {
                builtin::ensures(crate::M0::f()); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_requires_private code! {
        mod M1 {
            #[verifier::spec]
            fn f() -> bool { true }

            pub fn g() {
                builtin::requires(f());
            }
        }

        mod M2 {
            fn h() {
                crate::M1::g();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "public function requires cannot refer to private items")
}

test_verify_one_file! {
    #[test] test_publish_but_not_marked_pub verus_code! {
        #[verifier::spec]
        #[verifier(publish)]
        fn bar() -> u64 {
            7
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked #[verifier(publish)] but not marked `pub`")
}

test_verify_one_file! {
    #[test] publish_proof_fail code! {
        #[verifier::proof]
        #[verifier(publish)] /* vattr */
        pub fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked #[verifier(publish)] but not marked #[verifier::spec]")
}

test_verify_one_file! {
    #[test] publish_exec_fail code! {
        #[verifier(publish)] /* vattr */
        pub fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked #[verifier(publish)] but not marked #[verifier::spec]")
}

test_verify_one_file! {
    #[test] main_proof_fail code! {
        #[verifier::proof]
        pub fn main() {
        }
    } => Err(err) => assert_vir_error_msg(err, "`main` function should be #[verifier::exec]")
}

test_verify_one_file! {
    #[test] main_spec_fail code! {
        #[verifier::spec]
        pub fn main() {
            ()
        }
    } => Err(err) => assert_vir_error_msg(err, "`main` function should be #[verifier::exec]")
}

test_verify_one_file! {
    #[test] open_fn_refers_to_private_const_fail verus_code! {
        mod A {
            spec const X: usize = 1;
            pub open spec fn f() -> usize {
                X
            }
        }

        mod B {
            use crate::A;
            pub open spec fn g() -> bool {
                A::f() == 1
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "public spec function cannot refer to private items")
}
