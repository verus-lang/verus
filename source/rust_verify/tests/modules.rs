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
        #[verifier(publish)] #[verifier(opaque_outside_module)]
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

test_verify_one_file! {
    #[test] test_mod_child_ok code! {
        #[spec]
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
            #[spec]
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
            #[spec]
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
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_publish_but_not_marked_pub verus_code! {
        #[spec]
        #[verifier(publish)]
        fn bar() -> u64 {
            7
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] publish_proof_fail code! {
        #[proof]
        #[verifier(publish)]
        pub fn bar() {
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] publish_exec_fail code! {
        #[verifier(publish)]
        pub fn bar() {
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] main_proof_fail code! {
        #[proof]
        pub fn main() {
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] main_spec_fail code! {
        #[spec]
        pub fn main() {
            ()
        }
    } => Err(err) => assert_vir_error(err)
}
