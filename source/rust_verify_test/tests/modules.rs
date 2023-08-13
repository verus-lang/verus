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

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

const M1_OPAQUE: &str = verus_code_str! {
    mod M1 {
        #[derive(PartialEq, Eq)]
        pub struct Car {
            pub four_doors: bool,
        }

        #[verifier(opaque_outside_module)] /* vattr */
        pub open spec fn is_four_doors(c: Car) -> bool {
            c.four_doors
        }
    }
};

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_no_reveal M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use builtin::*;

            fn test() {
                let c = Car { four_doors: true };
                assert(is_four_doors(c)); // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_mod_fn_publish_opaque_reveal M1_OPAQUE.to_string() + verus_code_str! {
        mod M2 {
            use crate::M1::{is_four_doors, Car};
            use builtin::*;

            fn test() {
                let c = Car { four_doors: true };
                proof {
                    reveal(is_four_doors);
                }
                assert(is_four_doors(c));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_adt_no_verify verus_code! {
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
    #[test] test_mod_child_ok verus_code! {
        spec fn f() -> bool {
            true
        }

        mod M1 {
            fn test()
                ensures crate::f()
            {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mod_sibling_fail verus_code! {
        mod M0 {
            pub closed spec fn f() -> bool {
                true
            }
        }

        mod M1 {
            fn test()
                ensures crate::M0::f() // FAILS
            {
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_requires_private verus_code! {
        mod M1 {
            spec fn f() -> bool { true }

            pub fn g()
                requires f()
            {
            }
        }

        mod M2 {
            fn h() {
                crate::M1::g();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "in 'requires' clause of public function, cannot refer to private function")
}

test_verify_one_file! {
    #[test] test_publish_but_not_marked_pub verus_code! {
        open spec fn bar() -> u64 {
            7
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `open` but not marked `pub`")
}

test_verify_one_file! {
    #[test] publish_proof_fail verus_code! {
        #[verifier(publish)]
        pub proof fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `open` but it is not a `spec` function")
}

test_verify_one_file! {
    #[test] publish_exec_fail verus_code! {
        #[verifier(publish)]
        pub fn bar() {
        }
    } => Err(err) => assert_vir_error_msg(err, "function is marked `open` but it is not a `spec` function")
}

test_verify_one_file! {
    #[test] main_proof_fail verus_code! {
        pub proof fn main() {
        }
    } => Err(err) => assert_vir_error_msg(err, "`main` function should be #[verifier::exec]")
}

test_verify_one_file! {
    #[test] main_spec_fail verus_code! {
        pub closed spec fn main() {
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
    } => Err(err) => assert_vir_error_msg(err, "in pub open spec function, cannot refer to private const")
}
